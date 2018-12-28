import {expect} from 'chai';
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
          disjvars: new Set<[string, string]>(),
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
          activevariables: new Set<string>(),
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

    const old = console.error;
    let errors = 0;
    console.error = () => ++errors;

    fs.writeFileSync('test.txt', 'hello world', {encoding: 'utf8'});
    const hw: checkmm.std.IStream = new checkmm.std.IStream('test.txt');
    expect(checkmm.nexttoken(hw)).to.equal('hello');
    expect(checkmm.nexttoken(hw)).to.equal('world');
    expect(checkmm.nexttoken(hw)).to.equal('');
    expect(checkmm.nexttoken(hw)).to.equal('');
    expect(errors).to.equal(0);

    fs.writeFileSync('test.txt', String.fromCharCode(127), {encoding: 'utf8'});
    const invalid: checkmm.std.IStream = new checkmm.std.IStream('test.txt');
    expect(checkmm.nexttoken(invalid)).to.equal('');
    expect(errors).to.equal(1);

    console.error = old;
  });

  it('can read tokens', () => {
    checkmm.initTestValues({});
    const okay: boolean = checkmm.readtokens(__dirname + '/../node_modules/metamath-test/anatomy.mm');
    expect(okay).to.equal(true);
    expect(checkmm.tokens.length).to.equal(60);
  });

  it('can construct assertions with disjoint variables', () => {
    checkmm.initTestValues({
      scopes: [
        {
          activevariables: new Set<string>(),
          activehyp: [],
          disjvars: [new Set<string>(['ph', 'x'])],
          floatinghyp: {}
        }
      ],
      variables: new Set<string>(['ps', 'ph', 'x'])
    });
    const expression = '|- ( ph -> A. x ph )'.split(' ');
    const assertion: checkmm.Assertion = checkmm.constructassertion('ax-17', expression);
//    expect(assertion.hypotheses).to.equal(['wph', 'vx']);
    expect(assertion.disjvars.size).to.equal(1);
//    expect(assertion.disjvars.has(['ph', 'x'])).to.equal(true);
    expect(assertion.expression).to.equal(expression);
  });

});

