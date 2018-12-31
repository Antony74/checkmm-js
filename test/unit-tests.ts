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
          disjvars: [],
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
      hypotheses: {
        wph: {
          first: ['whp', 'ph'],
          second: true
        },
        vx: {
          first: ['vx', 'x'],
          second: true
        }
      },
      scopes: [
        {
          activevariables: new Set<string>(),
          activehyp: ['wph', 'vx'],
          disjvars: [new Set<string>()],
          floatinghyp: {}
        },
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
    expect(assertion.hypotheses).to.deep.equal(['wph', 'vx']);
    expect(assertion.disjvars).to.deep.equal([['ph', 'x']]);
    expect(assertion.expression).to.deep.equal(expression);
  });

  it('can read expressions', () => {
    checkmm.initTestValues({
      tokens: '|- ( ph -> ( ps -> ph ) ) $. $( Axiom _Frege_.'.split(' '),
      constants: ['|-', '(', ')', '->', 'ph', 'ps']
    });
    const expression: checkmm.Expression = checkmm.readexpression('a', 'ax-1', '$.');
    expect(expression).to.deep.equal('|- ( ph -> ( ps -> ph ) )'.split(' '));
  });

  it('can make substituions', () => {
    const expression: checkmm.Expression = checkmm.makesubstitution(
      ['weather', 'is', 'sunny'],
      {
        sunny: ['raining', 'cats', 'and', 'dogs']
      }
    );
    expect(expression).to.deep.equal(['weather', 'is', 'raining', 'cats', 'and', 'dogs']);
  });

  it('can get proof numbers', () => {
    const proofnumbers: number[] = checkmm.getproofnumbers(
      'pm5.32',
      'ABCDZEZABFZEZFZACFZEZFZDZABGZACGZDPAQTDZERUADUCOUFABCHIAQTJRUAHKUDSUEUBABLACLMN'
    );
    expect(proofnumbers).to.deep.equal([
      1, 2, 3, 4, 0, 5, 0, 1, 2, 6, 0, 5, 0, 6, 0, 1, 3, 6, 0, 5, 0, 6, 0, 4, 0, 1, 2, 7, 0, 1, 3, 7, 0, 4, 16, 1, 17, 20, 4, 0, 5,
      18, 21, 4, 23, 15, 26, 1, 2, 3, 8, 9, 1, 17, 20, 10, 18, 21, 8, 11, 24, 19, 25, 22, 1, 2, 12, 1, 3, 12, 13, 14
    ]);


  });

});

