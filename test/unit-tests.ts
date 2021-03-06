import * as fs from 'fs';
import {expect} from 'chai';
import fetchMock from 'fetch-mock';

import {Assertion, CheckMM, Expression, Scope, State, std} from '../src/checkmm';
import { CheckMMex } from '../src/checkmmex';

describe('checkmm-js', () => {

  it('can detect upper case', () => {
    expect(std.isupper('Z')).to.equal(true);
    expect(std.isupper('a')).to.equal(false);
  });

  it('can detect alphanumerics', () => {
    expect(std.isalnum('1')).to.equal(true);
    expect(std.isalnum(')')).to.equal(false);
  });

  it('can determine if a label is used', () => {

    const checkmm = new CheckMM();

    checkmm.setState({
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

    const checkmm = new CheckMM();

    checkmm.setState({
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

    const checkmm = new CheckMM();

    const old = console.error;
    let errors = 0;
    console.error = () => ++errors;

    let input = 'hello world';
    let token = '';

    ({token, input} = checkmm.nexttoken(input));
    expect(token).to.equal('hello');
    ({token, input} = checkmm.nexttoken(input));
    expect(token).to.equal('world');
    ({token, input} = checkmm.nexttoken(input));
    expect(token).to.equal('');
    ({token, input} = checkmm.nexttoken(input));
    expect(token).to.equal('');
    expect(errors).to.equal(0);

    input = String.fromCharCode(127);
    ({token, input} = checkmm.nexttoken(input));
    expect(token).to.equal('');
    expect(errors).to.equal(1);

    console.error = old;
  });

  it('can read tokens', () => {
    const checkmm = new CheckMM();
    const okay: boolean = checkmm.readtokens(__dirname + '/../../node_modules/metamath-test/anatomy.mm');
    expect(okay).to.equal(true);
    expect(checkmm.tokens.length).to.equal(60);
  });

  it('can construct assertions with disjoint variables', () => {

    const checkmm = new CheckMM();

    checkmm.setState({
      hypotheses: {
        wph: {
          first: ['wff', 'ph'],
          second: true
        },
        vx: {
          first: ['wff', 'x'],
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
    const assertion: Assertion = checkmm.constructassertion('ax-17', expression);
    expect(assertion.hypotheses).to.deep.equal(['wph', 'vx']);
    expect(assertion.disjvars).to.deep.equal([['ph', 'x']]);
    expect(assertion.expression).to.deep.equal(expression);
  });

  it('can read expressions', () => {

    const checkmm = new CheckMM();

    checkmm.setState({
      tokens: '|- ( ph -> ( ps -> ph ) ) $. $( Axiom _Frege_.'.split(' '),
      constants: ['|-', '(', ')', '->', 'ph', 'ps']
    });
    const expression: Expression = checkmm.readexpression('a', 'ax-1', '$.');
    expect(expression).to.deep.equal('|- ( ph -> ( ps -> ph ) )'.split(' '));
  });

  it('can make substituions', () => {

    const checkmm = new CheckMM();

    const expression: Expression = checkmm.makesubstitution(
      ['weather', 'is', 'sunny'],
      {
        sunny: ['raining', 'cats', 'and', 'dogs']
      }
    );
    expect(expression).to.deep.equal(['weather', 'is', 'raining', 'cats', 'and', 'dogs']);
  });

  it('can get proof numbers', () => {
    const checkmm = new CheckMM();
    const proofnumbers: number[] = checkmm.getproofnumbers(
      'pm5.32',
      'ABCDZEZABFZEZFZACFZEZFZDZABGZACGZDPAQTDZERUADUCOUFABCHIAQTJRUAHKUDSUEUBABLACLMN'
    );
    expect(proofnumbers).to.deep.equal([
      1, 2, 3, 4, 0, 5, 0, 1, 2, 6, 0, 5, 0, 6, 0, 1, 3, 6, 0, 5, 0, 6, 0, 4, 0, 1, 2, 7, 0, 1, 3, 7, 0, 4, 16, 1, 17, 20, 4, 0, 5,
      18, 21, 4, 23, 15, 26, 1, 2, 3, 8, 9, 1, 17, 20, 10, 18, 21, 8, 11, 24, 19, 25, 22, 1, 2, 12, 1, 3, 12, 13, 14
    ]);
  });

  it('can verify a proof step references an assertion', () => {
    const checkmm = new CheckMM();
    checkmm.setState({
      assertions: {
        'ax-mp': {
          hypotheses: ['wph', 'wps', 'min', 'maj'],
          disjvars: [],
          expression: ['|-', 'ps']
        }
      },
      hypotheses: {
        'wph': {
          first: ['wff', 'ph'],
          second: true
        },
        'wps': {
          first: ['wff', 'ps'],
          second: true
        },
        'min': {
          first: ['|-', 'ph'],
          second: false
        },
        'maj': {
          first: ['|-', '(', 'ph', '->', 'ps', ')'],
          second: false
        }
      }
    });

    const result: Expression[] = checkmm.verifyassertionref('mpdb', 'ax-mp', [
      ['wff', 'ps'],
      ['wff', 'ch'],
      ['wff', 'ph'],
      ['wff', 'ps'],
      ['|-', 'ph'],
      ['|-', '(', 'ph', '->', 'ps', ')']
    ]);

    expect(result).to.deep.equal([
      ['wff', 'ps'],
      ['wff', 'ch'],
      ['|-', 'ps']
    ]);
  });

  it('can verify a proof step references an assertion with disjoint variable conditions', () => {
    const checkmm = new CheckMM();
    checkmm.setState({
      assertions: {
        'ax-17': {
          hypotheses: ['wph', 'vx'],
          expression: ['|-', '(', 'ph', '->', 'A.', 'x', 'ph', ')'],
          disjvars: [['ph', 'x']]
        }
      },
      hypotheses: {
        'wph': {
          first: ['wff', 'ph'],
          second: true
        },
        'vx': {
          first: ['set', 'x'],
          second: true
        },
      },
      variables: new Set<string>(['ps', 'x']),
      scopes: [
        {
          activehyp: [],
          activevariables: new Set<string>(),
          floatinghyp: {},
          disjvars: [new Set<string>(['ps', 'x'])]
        }
      ]
    });

    const result: Expression[] = checkmm.verifyassertionref('a17d', 'ax-17', [
      ['wff', '(', 'ps', '->', 'A.', 'x', 'ps', ')'],
      ['wff', 'ph'],
      ['wff', 'ps'],
      ['set', 'x']
    ]);

    expect(result).to.deep.equal([
      ['wff', '(', 'ps', '->', 'A.', 'x', 'ps', ')'],
      ['wff', 'ph'],
      ['|-', '(', 'ps', '->', 'A.', 'x', 'ps', ')']
    ]);
  });

  function initStateForTh1(tokens: string[], checkmm: CheckMM) {
    const testValues: Partial<State> = {
      hypotheses: {
        tt: {
          first: ['term', 't'],
          second: true
        },
        tr: {
          first: ['term', 'r'],
          second: true
        },
        ts: {
          first: ['term', 's'],
          second: true
        },
        wp: {
          first: ['wff', 'P'],
          second: true
        },
        wq: {
          first: ['wff', 'Q'],
          second: true
        },
        min: {
          first: ['|-', 'P'],
          second: false
        },
        maj: {
          first: '|- ( P -> Q )'.split(' '),
          second: false
        }
      },
      assertions: {
        tze: {
          expression: ['term', '0'],
          disjvars: [],
          hypotheses: []
        },
        tpl: {
          expression: ['term', '(', 't', '+', 'r', ')'],
          disjvars: [],
          hypotheses: ['tt', 'tr']
        },
        weq: {
          expression: ['wff', 't', '=', 'r'],
          disjvars: [],
          hypotheses: ['tt', 'tr']
        },
        a1: {
          expression: '|- ( t = r -> ( t = s -> r = s ) )'.split(' '),
          disjvars: [],
          hypotheses: ['tt', 'tr', 'ts']
        },
        a2: {
          expression: ['|-', '(', 't', '+', '0', ')', '=', 't'],
          disjvars: [],
          hypotheses: ['tt']
        },
        mp: {
          expression: ['|-', 'Q'],
          disjvars: [],
          hypotheses: ['wp', 'wq', 'min', 'maj']
        },
        wim: {
          expression: ['wff', '(', 'P', '->', 'Q', ')'],
          disjvars: [],
          hypotheses: ['wp', 'wq']
        }
      },
      constants: ['(', ')', '+', '->', '0', '=', 'term', 'wff', '|-'],
      variables: new Set<string>(['P', 'Q', 'r', 's', 't']),
      tokens: tokens,
      scopes: [
        {
          activevariables: new Set<string>(['P', 'Q', 'r', 's', 't']),
          activehyp: ['tt', 'tr', 'ts', 'wp', 'wq'],
          disjvars: [],
          floatinghyp: {
            'P': 'wp',
            'Q': 'wq',
            'r': 'tr',
            's': 'ts',
            't': 'tt'
          }
        }
      ]
    };

    checkmm.setState(testValues);
  }

  it('can verify regular and compressed proofs', () => {

    const checkmm = new CheckMM();

    initStateForTh1([], checkmm);

    const theorem: Assertion = {
      hypotheses: ['tt'],
      disjvars: [],
      expression: ['|-', 't', '=', 't']
    };

    const proof: string[] = (
      'tt tze tpl tt weq tt tt weq tt a2 tt tze tpl ' +
      'tt weq tt tze tpl tt weq tt tt weq wim tt a2 ' +
      'tt tze tpl tt tt a1 mp mp'
    ).split(' ');

    const result1: boolean = checkmm.verifyregularproof('th1', theorem, proof);
    expect(result1).to.equal(true);
  });

  it('can verify compressed proofs', () => {

    const checkmm = new CheckMM();

    initStateForTh1([], checkmm);

    const labels = 'tze tpl weq a2 wim a1 mp'.split(' ');
    const proofnumbers = checkmm.getproofnumbers('th1', 'ABCZADZAADZAEZJJKFLIAAGHH');

    const theorem: Assertion = {
      hypotheses: ['tt'],
      disjvars: [],
      expression: ['|-', 't', '=', 't']
    };

    const result2: boolean = checkmm.verifycompressedproof('th1', theorem, labels, proofnumbers);
    expect(result2).to.equal(true);
  });

  it('can parse $p statements for regular proofs', () => {
    const checkmm = new CheckMM();
    initStateForTh1((
      '|- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl tt weq tt tze tpl tt weq tt tt weq ' +
      'wim tt a2 tt tze tpl tt tt a1 mp mp $.'
    ).split(' '), checkmm);

    const okay: boolean = checkmm.parsep('th1');
    expect(okay).to.equal(true);
  });

  it('can parse $p statements for compressed proofs', () => {
    const checkmm = new CheckMM();
    initStateForTh1((
      '|- t = t $= ( tze tpl weq a2 wim a1 mp ) ABCZADZAADZAEZJJKFLIAAGHH $.'
    ).split(' '), checkmm);

    const okay: boolean = checkmm.parsep('th1');
    expect(okay).to.equal(true);
  });

  it('can parse $c statements', () => {
    const checkmm = new CheckMM();
    checkmm.setState({
      scopes: [new Scope()],
      tokens: '0 + = -> ( ) term wff |- $.'.split(' ')
    });

    const okay = checkmm.parsec();
    expect(okay).to.equal(true);
  });

  it('can verify demo0.mm', () => {

    const old = console.log;
    console.log = () => {};

    const checkmm = new CheckMM();
    checkmm.setState({});

    let okay: boolean = checkmm.readtokens(__dirname + '/../../node_modules/metamath-test/demo0.mm');
    expect(okay).to.equal(true);

    okay = checkmm.checkmm();
    expect(okay).to.equal(true);

    console.log = old;
  });

  it('can asynchronously verify demo0.mm', (done) => {

    const old = console.log;
    console.log = () => {};

    const url = 'http://loclhost:8080/demo0.mm';

    const checkmm = new CheckMMex();

    fetchMock.get('*', fs.readFileSync(__dirname + '/../../node_modules/metamath-test/demo0.mm', {encoding: 'utf8'}));

    checkmm.readTokensAsync(url, (error: string) => {
      expect(error).to.equal('');
      expect(checkmm.getState().tokens.length).to.equal(166);
      const okay: boolean = checkmm.checkmm();
      expect(okay).to.equal(true);

      console.log = old;

      done();
    });
  });

});

