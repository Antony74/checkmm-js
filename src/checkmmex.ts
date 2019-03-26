import {CheckMM, Input} from './checkmm';

export class CheckMMex extends CheckMM {

  readTokensAsync(url: string, callback: (ok: boolean, message: string) => void): void {
    this.readTokensAsync2(url, '', callback);
  }

  private readTokensAsync2(url: string, existingInput: string, callback: (ok: boolean, message: string) => void): void {

    const doCallback = () => {
      if (this.state.errors.length) {
        callback(false, this.state.errors);
      } else {
        callback(true, this.state.logs);
      }
    };

    const alreadyencountered: boolean = this.state.mmFileNames.has(url);
    if (alreadyencountered) {
      doCallback();
      return;
    }

    this.state.mmFileNames.add(url);

    fetch(url).then((response: Response) => {
      if (!response.ok) {
        this.error('Failed to fetch "' + url + '": ' + response.statusText);
        doCallback();
      } else {
        response.text().then((text: string) => {
          const input: Input = new Input(text + existingInput);
          let incomment = false;
          let infileinclusion = false;
          let newfilename: string = '';

          let token: string = '';
          while (true) {
            token = this.nexttoken(input);
            if (!token.length) {
              break;
            }

            if (incomment) {
              if (token === '$)') {
                incomment = false;
                continue;
              }
              if (token.indexOf('$(') !== -1) {
                this.error('Characters $( found in a comment');
                doCallback();
                return;
              }
              if (token.indexOf('$)') !== -1) {
                this.error('Characters $) found in a comment');
                doCallback();
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
                  this.error('Filename ' + token + ' contains a $');
                  doCallback();
                  return;
                }
                newfilename = token;
                continue;
              } else {
                if (token !== '$]') {
                  this.error('Didn\'t find closing file inclusion delimiter');
                  doCallback();
                  return;
                }

                const pieces = url.split('/');
                pieces.pop();
                pieces.push(newfilename);
                this.readTokensAsync2(pieces.join('/'), input.toString(), callback);
                return;
              }
            }
            if (token === '$[') {
              infileinclusion = true;
              continue;
            }

            this.state.tokens.push(token);
          }

          if (incomment) {
            this.error('Unclosed comment');
            doCallback();
            return;
          }

          if (infileinclusion) {
            this.error('Unfinished file inclusion command');
            doCallback();
            return;
          }

          doCallback();
        }).catch((e) => {
          this.error('Failed while fetching ' + url);
          doCallback();
        });
      }
    }).catch((e) => {
      this.error('Failed to fetch ' + url);
      doCallback();
    });

  }

}

