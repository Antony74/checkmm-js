import {expect} from 'chai';
import * as checkmm from '../src/checkmm';

describe('checkmm-js', () => {
  it('can detect upper case', () => {
    expect(checkmm.std.isupper('Z')).to.equal(true);
    expect(checkmm.std.isupper('a')).to.equal(false);
  });
});

