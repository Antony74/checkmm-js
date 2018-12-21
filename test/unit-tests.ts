import {expect} from 'chai';
const streamMock = require('stream-mock');
import * as fs from 'fs';

import * as checkmm from '../src/checkmm';


describe('checkmm-js', () => {

  it('can detect upper case', () => {
    expect(checkmm.std.isupper('Z')).to.equal(true);
    expect(checkmm.std.isupper('a')).to.equal(false);
  });

  it('can detect alphanumerics', () => {
    expect(checkmm.std.isalnum('1')).to.equal(true);
    expect(checkmm.std.isalnum(')')).to.equal(false);
  });

  it('can determine if a label is used', () => {
    checkmm.initTestValues({
      hypotheses: {
        hello: {
          first: ['my', 'hypothesis'],
          second: false
        }
      },
      assertions: {
        world: {
          hypotheses: [],
          disjvars: {},
          expression: []
        }
      }
    });

    expect(checkmm.labelused('hello')).to.equal(true);
    expect(checkmm.labelused('meaningless')).to.equal(false);
    expect(checkmm.labelused('world')).to.equal(true);
  });

  it('can find a floating hypothesis', () => {
    checkmm.initTestValues({
      scopes: [
        {
          activevariables: {},
          activehyp: [],
          disjvars: [],
          floatinghyp: {
            hello: 'world'
          }
        }
      ]
    });

    expect(checkmm.getfloatinghyp('hello')).to.equal('world');
    expect(checkmm.getfloatinghyp('other')).to.equal('');
  });

  it('can get the next token', () => {
    const hw = new streamMock.ReadableMock('hello world', {encoding: 'utf8'});
    expect(checkmm.nexttoken(hw)).to.equal('hello');
    expect(checkmm.nexttoken(hw)).to.equal('world');
    expect(checkmm.nexttoken(hw)).to.equal('');
    expect(checkmm.nexttoken(hw)).to.equal('');

    const invalid = new streamMock.ReadableMock(String.fromCharCode(127), {encoding: 'utf8'});
    expect(checkmm.nexttoken(invalid)).to.equal('');
  });

});

