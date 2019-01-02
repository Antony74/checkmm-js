// Metamath database verifier
// Antony Bartlett (akb@akb.me.uk)
//
// I release this code to the public domain under the
// Creative Commons "CC0 1.0 Universal" Public Domain Dedication:
//
// http://creativecommons.org/publicdomain/zero/1.0/
//
// This is a port to TypeScript.  The original C++ program was
// written by Eric Schmidt and can be found here:
// http://us.metamath.org/other.html#checkmm
//
// This is a standalone verifier for Metamath database files.
// Run it with a single file name as the parameter.
//
// Some notes:
//
// The code assumes that the character set is compatible with ASCII.
//
// According to the spec, file inclusion commands should not include a file
// that has already been included. Unfortunately, determing whether two
// different strings refer to the same file is not easy, and, worse, is
// system-dependant. This program ignores the issue entirely and assumes
// that distinct strings name different files. This should be adequate for
// the present, at least.
//
// If the verifier finds an error, it will report it and quit. It will not
// attempt to recover and find more errors. The only condition that generates
// a diagnostic message but doesn't halt the program is an incomplete proof,
// specified by a question mark. In that case, as per the spec, a warning is
// issued and checking continues.
//
// Please let me know of any bugs.
// https://github.com/Antony74/checkmm-js/issues

import * as fs from 'fs';

export namespace std {

  export function isupper(s: string): boolean {
    if ( /[^A-Z]/.test(s)) {
      return false;
    } else {
      return true;
    }
  }

  export function isalnum(s: string): boolean {
    if ( /[^a-zA-Z0-9]/.test(s)) {
      return false;
    } else {
      return true;
    }
  }

  export function set_intersection<T>(s1: Set<T>, s2: Set<T>): Set<T> {
    const s3 = new Set<T>();
    s1.forEach((value: T) => {
      if (s2.has(value)) {
        s3.add(value);
      }
    });
    return s3;
  }

  export class IStream {
    private fd: number;
    private buffer: Buffer = Buffer.alloc(1);
    private arr: string[] = [];

    constructor(filename: string) {
      this.fd = fs.openSync(filename, 'r');
    }

    get(): string {
      if (this.arr.length) {
        return this.arr.shift();
      } else {
        const bytesRead = fs.readSync(this.fd, this.buffer, 0, 1, null);
        return (bytesRead === 1) ? this.buffer.toString() : null;
      }
    }

    unget(s: string) {
      this.arr.unshift(s);
    }
  }

  export class Pair<T1, T2> {
    first: T1;
    second: T2;
  }
}


export let tokens: string[] = [];

let constants: string[] = [];

export type Expression = string[];

// The first parameter is the statement of the hypothesis, the second is
// true iff the hypothesis is floating.
type Hypothesis = std.Pair<Expression, boolean>;

let hypotheses: {[token: string]: Hypothesis} = {};

let variables: Set<string> = new Set<string>();

// An axiom or a theorem.
export class Assertion {
  // Hypotheses of this axiom or theorem.
  hypotheses: string[] = [];
  disjvars: [string, string][] = [];

  // Statement of axiom or theorem.
  expression: Expression = [];
}

let assertions: {[token: string]: Assertion} = {};

class Scope {
  activevariables: Set<string> = new Set<string>();
  // Labels of active hypotheses
  activehyp: string[] = [];
  disjvars: Set<string>[] = [];
  // Map from variable to label of active floating hypothesis
  floatinghyp: {[token: string]: string} = {};
}

let scopes: Scope[] = [];

interface State {
  tokens: string[];
  hypotheses: {[token: string]: Hypothesis};
  assertions: {[token: string]: Assertion};
  scopes: Scope[];
  variables: Set<string>;
  constants: string[];
}

export function initTestValues(state: Partial<State>) {
  ({tokens, hypotheses, assertions, scopes, variables, constants} = {
    tokens: [],
    hypotheses: {},
    assertions: {},
    scopes: [],
    variables: new Set<string>(),
    constants: [],
    ...state
  });
}

const nProofCount: number = 0;
const nProofLimit: number = Number.MAX_SAFE_INTEGER;

// Determine if a string is used as a label
export function labelused(label: string): boolean {
  return (hypotheses[label] || assertions[label]) ? true : false;
}

// Find active floating hypothesis corresponding to variable, or empty string
// if there isn't one.
export function getfloatinghyp(variable: string): string {
  for (let nScope = 0; nScope < scopes.length; ++nScope) {
    const loc: string = scopes[nScope].floatinghyp[variable];
    if (loc !== undefined) {
      return loc;
    }
  }

  return '';
}

export function isactivevariable(str: string): boolean {
  for (let nScope = 0; nScope < scopes.length; ++nScope) {
    if (scopes[nScope].activevariables.has(str)) {
      return true;
    }
  }
  return false;
}

export function isactivehyp(str: string): boolean {
  for (let nScope = 0; nScope < scopes.length; ++nScope) {
    if (scopes[nScope].activehyp.find((value) => value === str) !== undefined) {
      return true;
    }
  }
  return false;
}

// Determine if there is an active disjoint variable restriction on
// two different variables.
export function isdvr(var1: string, var2: string) {
  if (var1 === var2) {
    return false;
  }
  for (let nScope = 0; nScope < scopes.length; ++nScope) {
    const scope = scopes[nScope];
    for (let nDisjvar = 0; nDisjvar !== scope.disjvars.length; ++nDisjvar) {
      const disjvar = scope.disjvars[nDisjvar];
      if (disjvar.has(var1)
      &&  disjvar.has(var2)) {
        return true;
      }
    }
  }
  return false;
}

// Determine if a character is white space in Metamath.
export function ismmws(ch: string): boolean {
  // This doesn't include \v ("vertical tab"), as the spec omits it.
  return ch === ' ' || ch === '\n' || ch === '\t' || ch === '\f' || ch === '\r';
}

// Determine if a token is a label token.
export function islabeltoken(token: string): boolean {
  for (let nCh = 0; nCh < token.length; ++nCh) {
    const ch = token[nCh];
    if (!std.isalnum(ch) || ch === '.' || ch === '-' || ch === '_') {
      return false;
    }
  }
  return true;
}

// Determine if a token is a math symbol token.
export function ismathsymboltoken(token: string): boolean {
  return token.indexOf('$') !== -1;
}

// Determine if a token consists solely of upper-case letters or question marks
export function containsonlyupperorq(token: string): boolean {
  for (let nCh = 0; nCh < token.length; ++nCh) {
    const ch = token[nCh];
    if (!std.isupper(ch) && ch !== '?') {
      return false;
    }
  }
  return true;
}

export function nexttoken(input: std.IStream): string {
  let ch: string = null;
  let token: string = '';

  // Skip whitespace
  while (true) {
    ch = input.get();
    if (ch === null || !ismmws(ch)) {
      break;
    }
  }

  if (ch !== null) {
    input.unget(ch);
  }

  // Get token
  while (true) {
    ch = input.get();

    if (ch === null || ismmws(ch)) {
      break;
    }

    if (ch < '!' || ch > '~') {
      console.error('Invalid character read with code ' + ch.charCodeAt(0));
      return '';
    }

    token += ch;
  }

  return token;
}

const names: Set<string> = new Set<string>();

export function readtokens(filename: string): boolean {
  const alreadyencountered: boolean = names.has(filename);
  if (alreadyencountered) {
    return true;
  }

  names.add(filename);

  const fin = new std.IStream(filename);

  let incomment = false;
  let infileinclusion = false;
  let newfilename: string = '';

  let token: string = '';
  while (true) {
    token = nexttoken(fin);
    if (!token.length) {
      break;
      }

    if (incomment) {
      if (token === '$)') {
        incomment = false;
        continue;
      }
      if (token.indexOf('$(') !== -1) {
        console.error('Characters $( found in a comment');
        return false;
      }
      if (token.indexOf('$)') !== -1) {
        console.error('Characters $) found in a comment');
        return false;
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
          console.error('Filename ' + token + ' contains a $');
          return false;
        }
        newfilename = token;
        continue;
      } else {
        if (token !== '$]') {
          console.error('Didn\'t find closing file inclusion delimiter');
          return false;
        }

        const okay: boolean = readtokens(newfilename);
        if (!okay) {
          return false;
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

    tokens.push(token);
  }

  if (incomment) {
    console.error('Unclosed comment');
    return false;
  }

  if (infileinclusion) {
      console.error('Unfinished file inclusion command');
      return false;
  }

  return true;
}

// Construct an Assertion from an Expression. That is, determine the
// mandatory hypotheses and disjoint variable restrictions.
// The Assertion is inserted into the assertions collection,
// and is returned.
export function constructassertion(label: string, exp: Expression): Assertion {
  const assertion: Assertion = new Assertion();

  assertion.expression = exp;

  const varsused: Set<string> = new Set<string>();

  // Determine variables used and find mandatory hypotheses

  for (let n = 0; n < exp.length; ++n) {
    const variable = exp[n];
    if (variables.has(variable)) {
      varsused.add(variable);
    }
  }

  for (let nScope = scopes.length - 1; nScope >= 0; --nScope) {
    const hypvec: string[] = scopes[nScope].activehyp;
    for (let n = hypvec.length - 1; n >= 0; --n) {
      const hyp: Hypothesis = hypotheses[hypvec[n]];
      if (hyp.second && varsused.has(hyp.first[1])) {
        // Mandatory floating hypothesis
        assertion.hypotheses.unshift(hypvec[n]);
      } else if (!hyp.second) {
        // Essential hypothesis
        assertion.hypotheses.unshift(hypvec[n]);
        for (let nExpression = 0; nExpression < hyp.first.length; ++nExpression) {
          if (variables.has(hyp.first[nExpression]) === null) {
            varsused.add(hyp.first[nExpression]);
          }
        }
      }
    }
  }

  // Determine mandatory disjoint variable restrictions
  for (let nScope = 0; nScope < scopes.length; ++nScope) {
    const disjvars: Set<string>[] = scopes[nScope].disjvars;
    for (let nDisjvars = 0; nDisjvars < disjvars.length; ++ nDisjvars) {
      const dset: string[] = [];
      std.set_intersection(disjvars[nDisjvars], varsused).forEach((value) => {
        dset.push(value);
      });

      for (let n = 0; n < dset.length; ++n) {
        for (let n2 = n + 1; n2 < dset.length; ++n2) {
          assertion.disjvars.push([dset[n], dset[n2]]);
        }
      }
    }
  }

  assertions[label] = assertion;
  return assertion;
}

// Read an expression from the token stream.
export function readexpression(stattype: string, label: string, terminator: string): Expression {

  const exp: Expression = [];

  if (!tokens.length) {
    console.error('Unfinished $' + stattype + ' statement ' + label);
    return null;
  }

  const type: string = tokens[0];

  if (constants.find((value) => type === value) === undefined) {
    console.error('First symbol in $' + stattype + ' statement ' + label + ' is ' + type + ' which is not a constant');
    return null;
  }

  tokens.shift();

  exp.push(type);

  while (tokens.length) {
    const token = tokens.shift();

    if (token === terminator) {
      break;
    }

    if (constants.find((value) => value === token) === undefined
    &&  getfloatinghyp(token).length === 0) {
      console.error('In $' + stattype + ' statement ' + label
                  + ' token ' + token
                  + ' found which is not a constant or variable in an'
                  + ' active $f statement');
      return null;
    }

    exp.push(token);
  }

  if (!tokens.length) {
    console.error('Unfinished $' + stattype + ' statement ' + label);
    return null;
  }

  return exp;
}

// Make a substitution of variables. The result is put in "destination".
export function makesubstitution(original: Expression, substmap: {[label: string]: Expression}): Expression {
  let destination: Expression = [];
  for (let n = 0; n < original.length; ++n) {
    const substitution = substmap[original[n]];
    if (substitution === undefined) {
      // Constant
      destination.push(original[n]);
    } else {
      destination = [...destination, ...substitution];
    }
  }
  return destination;
}

export function getproofnumbers(label: string, proof: string): number[] {
  const proofnumbers: number[] = [];
  let num = 0;
  let justgotnum = false;
  for (let n = 0; n < proof.length; ++n) {
    if (proof[n] <= 'T') {
      const addval: number = proof.charCodeAt(n) - ('A'.charCodeAt(0) - 1);

      if (num > Number.MAX_SAFE_INTEGER / 20 || 20 * num > Number.MAX_SAFE_INTEGER - addval) {
        console.error('Overflow computing numbers in compressed proof of ' + label);
        return null;
      }

      proofnumbers.push((20 * num) + addval);
      num = 0;
      justgotnum = true;
    } else if (proof[n] <= 'Y') {
      const addval: number = proof.charCodeAt(n) - 'T'.charCodeAt(0);

      if (num > Number.MAX_SAFE_INTEGER / 5 || 5 * num > Number.MAX_SAFE_INTEGER - addval) {
        console.error('Overflow computing numbers in compressed proof of ' + label);
        return null;
      }

      num = (5 * num) + addval;
      justgotnum = false;
    } else { // It must be Z
      if (!justgotnum) {
        console.error('Stray Z found in compressed proof of ' + label);
        return null;
      }

      proofnumbers.push(0);
      justgotnum = false;
    }
  }

  if (num !== 0) {
    console.error('Compressed proof of theorem ' + label + ' ends in unfinished number');
    return null;
  }

  return proofnumbers;
}

// Subroutine for proof verification. Verify a proof step referencing an
// assertion (i.e., not a hypothesis).
export function verifyassertionref(thlabel: string, reflabel: string, stack: Expression[]): Expression[] {
  const assertion: Assertion = assertions[reflabel];

  if (!assertion) {
    console.error('In proof of theorem ' + thlabel + ' assertion ' + reflabel + ' is undefined');
    return null;
  }

  if (stack.length < assertion.hypotheses.length) {
    console.error('In proof of theorem ' + thlabel + ' not enough items found on stack');
    return null;
  }

  const base: number = stack.length - assertion.hypotheses.length;

  const substitutions: {[label: string]: Expression} = {};

  // Determine substitutions and check that we can unify
  for (let i = 0; i < assertion.hypotheses.length; ++i) {
    const hypothesis: Hypothesis = hypotheses[assertion.hypotheses[i]];

    if (!hypothesis) {
      console.error('In proof of theorem ' + thlabel + ' hypothesis ' + assertion.hypotheses[i] + ' is undefined');
      return null;
    }

    if (hypothesis.second) {
      // Floating hypothesis of the referenced assertion
      if (hypothesis.first[0] !== stack[base + i][0]) {
        console.error('In proof of theorem ' + thlabel + ' unification failed');
        return null;
      }

      const subst: Expression = stack[base + i].slice(1);
      substitutions[hypothesis.first[1]] = subst;
    } else {
      // Essential hypothesis
      const dest: Expression = makesubstitution(hypothesis.first, substitutions);
      if (JSON.stringify(dest) !== JSON.stringify(stack[base + i])) {
        console.error('In proof of theorem ' + thlabel + ' unification failed');
        return null;
      }
    }
  }

  // Remove hypotheses from stack
  stack = stack.slice(0, base);

  // Verify disjoint variable conditions
  for (let nDisjvar = 0; nDisjvar < assertion.disjvars.length; ++nDisjvar) {
    const exp1: Expression = substitutions[assertion.disjvars[nDisjvar][0]];
    const exp2: Expression = substitutions[assertion.disjvars[nDisjvar][1]];

    const exp1vars: string[] = [];
    for (let nExp1 = 0; nExp1 < exp1.length; ++nExp1) {
      if (variables.has(exp1[nExp1])) {
        exp1vars.push(exp1[nExp1]);
      }
    }

    const exp2vars: string[] = [];
    for (let nExp2 = 0; nExp2 < exp2.length; ++nExp2) {
      if (variables.has(exp2[nExp2])) {
        exp2vars.push(exp2[nExp2]);
      }
    }

    for (let nExp1 = 0; nExp1 < exp1vars.length; ++nExp1) {
      for (let nExp2 = 0; nExp2 < exp2vars.length; ++nExp2) {
        if (!isdvr(exp1vars[nExp1], exp2vars[nExp2])) {
          console.error('In proof of theorem ' + thlabel + ' disjoint variable restriction violated');
          return null;
        }
      }
    }
  }

  // Done verification of this step. Insert new statement onto stack.
  const result: Expression = makesubstitution(assertion.expression, substitutions);
  stack.push(result);
  return stack;
}

// Verify a regular proof. The "proof" argument should be a non-empty sequence
// of valid labels. Return true iff the proof is correct.
export function verifyregularproof(label: string, theorem: Assertion, proof: string[]): boolean {
  let stack: Expression[] = [];
  for (let n = 0; n < proof.length; ++n) {
    // If step is a hypothesis, just push it onto the stack.
    const hyp: Hypothesis = hypotheses[proof[n]];
    if (hyp) {
      stack.push(hyp.first);
      continue;
    }

    // It must be an axiom or theorem
    stack = verifyassertionref(label, proof[n], stack);
    if (stack === null) {
      return false;
    }
  }

  if (stack.length !== 1) {
    console.error('Proof of theorem ' + label + ' does not end with only one item on the stack');
    return false;
  }

  if (JSON.stringify(stack[0]) !== JSON.stringify(theorem.expression)) {
    console.error('Proof of theorem ' + label + ' proves wrong statement');
    return false;
  }

  return true;
}

