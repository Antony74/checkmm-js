import {CheckMM} from './checkmm';
import * as superagent from 'superagent';

export class CheckMMex extends CheckMM {
  superagent = superagent;
}

