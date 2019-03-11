import {CheckMM} from './checkmm';

export class CheckMMex extends CheckMM {

  readTokensAsync(url: string, callback: (error: string) => void): void {

    const alreadyencountered: boolean = this.state.mmFileNames.has(url);
    if (alreadyencountered) {
      callback('');
      return;
    }

    this.state.mmFileNames.add(url);

    fetch(url).then((response: Response) => {
      if (!response.ok) {
        callback('Failed to fetch "' + url + '": ' + response.statusText);
      } else {
        response.text().then((input: string) => {
          let incomment = false;
          let infileinclusion = false;
          let newfilename: string = '';

          let token: string = '';
          while (true) {
            ({token, input} = this.nexttoken(input));
            if (!token.length) {
              break;
            }

            if (incomment) {
              if (token === '$)') {
                incomment = false;
                continue;
              }
              if (token.indexOf('$(') !== -1) {
                callback('Characters $( found in a comment');
                return;
              }
              if (token.indexOf('$)') !== -1) {
                callback('Characters $) found in a comment');
                return;
              }
              continue;
            }

            // Not in comment
            if (token === '$(') {
                incomment = true;
                continue;
            }

            if (infileinclusion) {
              if (!newfilename.length) {
                if (token.indexOf('$') !== -1) {
                  callback('Filename ' + token + ' contains a $');
                  return;
                }
                newfilename = token;
                continue;
              } else {
                if (token !== '$]') {
                  callback('Didn\'t find closing file inclusion delimiter');
                  return;
                }

                const okay: boolean = this.readtokens(newfilename);
                if (!okay) {
                  return;
                }
                infileinclusion = false;
                newfilename = '';
                continue;
              }
            }
            if (token === '$[') {
              infileinclusion = true;
              continue;
            }

            this.state.tokens.push(token);
          }

          if (incomment) {
            callback('Unclosed comment');
            return;
          }

          if (infileinclusion) {
            callback('Unfinished file inclusion command');
            return;
          }

          callback('');
        });
      }
    });

  }

}

