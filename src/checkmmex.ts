import {CheckMM} from './checkmm';
import * as superagent from 'superagent';

export class CheckMMex extends CheckMM {

  superagent = superagent;

  readTokensAsync(url: string, callback: (error: string, tokens: string[]) => void) {
    this.superagent.get(url).then((response: superagent.Response) => {
      callback('', []);
    });
  }
}

