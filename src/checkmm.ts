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
import * as path from 'path';
import cloneDeep from 'lodash.clonedeep';

// checkmm uses a little bit of C++'s Standard Template Library.  Simulate it.
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

  export class Pair<T1, T2> {
    first: T1;
    second: T2;
  }
}

// Simple function for comparing arrays (in C++ STL handles this automatically)
function arraysequal(arr1: any[], arr2: any[]): boolean {

  if (arr1.length !== arr2.length) {
    return false;
  }

  for (let n = 0; n < arr1.length; ++n) {
    if (arr1[n] !== arr2[n]) {
      return false;
    }
  }

  return true;
}

interface NextToken {
  token: string;
  input: string;
}

export type Expression = string[];

// The first parameter is the statement of the hypothesis, the second is
// true iff the hypothesis is floating.
type Hypothesis = std.Pair<Expression, boolean>;

// An axiom or a theorem.
export class Assertion {
  // Hypotheses of this axiom or theorem.
  hypotheses: string[] = [];
  disjvars: [string, string][] = [];

  // Statement of axiom or theorem.
  expression: Expression = [];
}

export class Scope {
  activevariables: Set<string> = new Set<string>();
  // Labels of active hypotheses
  activehyp: string[] = [];
  disjvars: Set<string>[] = [];
  // Map from variable to label of active floating hypothesis
  floatinghyp: {[token: string]: string} = {};
}

export class State {
  tokens: string[] = [];
  constants: string[] = [];
  hypotheses: {[token: string]: Hypothesis} = {};
  variables: Set<string> = new Set<string>();
  assertions: {[token: string]: Assertion} = {};
  scopes: Scope[] = [];
  nProofCount: number = 0;
  nProofLimit: number = Number.MAX_SAFE_INTEGER;
  mmFileNames: Set<string> = new Set<string>();
}

export class CheckMM extends State {

  setState(partialState: Partial<State>) {

    const defaultState = new State();
    const state = {
      ...defaultState,
      ...cloneDeep(partialState)
    };

    Object.keys(state).forEach((key: string) => {
      this[key] = state[key];
    });
  }

  getState(): State {
    const state = new State();

    Object.keys(state).forEach((key: string) => {
      state[key] = this[key];
    });

    return cloneDeep(state);
  }

  // Determine if a string is used as a label
  labelused(label: string): boolean {
    return (this.hypotheses[label] || this.assertions[label]) ? true : false;
  }

  // Find active floating hypothesis corresponding to variable, or empty string
  // if there isn't one.
  getfloatinghyp(variable: string): string {
    for (let nScope = 0; nScope < this.scopes.length; ++nScope) {
      const loc: string = this.scopes[nScope].floatinghyp[variable];
      if (loc !== undefined) {
        return loc;
      }
    }

    return '';
  }

  isactivevariable(str: string): boolean {
    for (let nScope = 0; nScope < this.scopes.length; ++nScope) {
      if (this.scopes[nScope].activevariables.has(str)) {
        return true;
      }
    }
    return false;
  }

  isactivehyp(str: string): boolean {
    for (let nScope = 0; nScope < this.scopes.length; ++nScope) {
      if (this.scopes[nScope].activehyp.find((value) => value === str) !== undefined) {
        return true;
      }
    }
    return false;
  }

  // Determine if there is an active disjoint variable restriction on
  // two different variables.
  isdvr(var1: string, var2: string) {
    if (var1 === var2) {
      return false;
    }
    for (let nScope = 0; nScope < this.scopes.length; ++nScope) {
      const scope = this.scopes[nScope];
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
  ismmws(ch: string): boolean {
    // This doesn't include \v ("vertical tab"), as the spec omits it.
    return ch === ' ' || ch === '\n' || ch === '\t' || ch === '\f' || ch === '\r';
  }

  // Determine if a token is a label token.
  islabeltoken(token: string): boolean {
    for (let nCh = 0; nCh < token.length; ++nCh) {
      const ch = token[nCh];
      if (!(std.isalnum(ch) || ch === '.' || ch === '-' || ch === '_')) {
        return false;
      }
    }
    return true;
  }

  // Determine if a token is a math symbol token.
  ismathsymboltoken(token: string): boolean {
    return token.indexOf('$') === -1;
  }

  // Determine if a token consists solely of upper-case letters or question marks
  containsonlyupperorq(token: string): boolean {
    for (let nCh = 0; nCh < token.length; ++nCh) {
      const ch = token[nCh];
      if (!std.isupper(ch) && ch !== '?') {
        return false;
      }
    }
    return true;
  }

  nexttoken(input: string): NextToken {
    let ch: string = null;
    let token: string = '';

    // Skip whitespace
    while (input.length) {
      ch = input[0];
      input = input.slice(1);
      if (ch === null || !this.ismmws(ch)) {
        break;
      }
    }

    if (ch !== null) {
      input = ch + input;
    }

    // Get token
    while (input.length) {
      ch = input[0];
      input = input.slice(1);

      if (ch === null || this.ismmws(ch)) {
        break;
      }

      if (ch < '!' || ch > '~') {
        console.error('Invalid character read with code ' + ch.charCodeAt(0));
        return {token: '', input: input};
      }

      token += ch;
    }

    return {token: token, input: input};
  }

  readtokens(filename: string): boolean {
    const alreadyencountered: boolean = this.mmFileNames.has(filename);
    if (alreadyencountered) {
      return true;
    }

    this.mmFileNames.add(filename);

    let input = fs.readFileSync(filename, {encoding: 'utf8'});

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

          const okay: boolean = this.readtokens(newfilename);
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

      this.tokens.push(token);
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
  constructassertion(label: string, exp: Expression): Assertion {
    const assertion: Assertion = new Assertion();

    assertion.expression = exp;

    const varsused: Set<string> = new Set<string>();

    // Determine variables used and find mandatory hypotheses

    for (let n = 0; n < exp.length; ++n) {
      const variable = exp[n];
      if (this.variables.has(variable)) {
        varsused.add(variable);
      }
    }

    for (let nScope = this.scopes.length - 1; nScope >= 0; --nScope) {
      const hypvec: string[] = this.scopes[nScope].activehyp;
      for (let n = hypvec.length - 1; n >= 0; --n) {
        const hyp: Hypothesis = this.hypotheses[hypvec[n]];
        if (hyp.second && varsused.has(hyp.first[1])) {
          // Mandatory floating hypothesis
          assertion.hypotheses.unshift(hypvec[n]);
        } else if (!hyp.second) {
          // Essential hypothesis
          assertion.hypotheses.unshift(hypvec[n]);
          for (let nExpression = 0; nExpression < hyp.first.length; ++nExpression) {
            if (this.variables.has(hyp.first[nExpression])) {
              varsused.add(hyp.first[nExpression]);
            }
          }
        }
      }
    }

    // Determine mandatory disjoint variable restrictions
    for (let nScope = 0; nScope < this.scopes.length; ++nScope) {
      const disjvars: Set<string>[] = this.scopes[nScope].disjvars;
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

    this.assertions[label] = assertion;
    return assertion;
  }

  // Read an expression from the token stream.
  readexpression(stattype: string, label: string, terminator: string): Expression {

    const exp: Expression = [];

    if (!this.tokens.length) {
      console.error('Unfinished $' + stattype + ' statement ' + label);
      return null;
    }

    const type: string = this.tokens[0];

    if (this.constants.find((value) => type === value) === undefined) {
      console.error('First symbol in $' + stattype + ' statement ' + label + ' is ' + type + ' which is not a constant');
      return null;
    }

    this.tokens.shift();

    exp.push(type);

    while (this.tokens.length) {
      const token = this.tokens.shift();

      if (token === terminator) {
        break;
      }

      if (this.constants.find((value) => value === token) === undefined
      &&  this.getfloatinghyp(token).length === 0) {
        console.error('In $' + stattype + ' statement ' + label
                    + ' token ' + token
                    + ' found which is not a constant or variable in an'
                    + ' active $f statement');
        return null;
      }

      exp.push(token);
    }

    if (!this.tokens.length) {
      console.error('Unfinished $' + stattype + ' statement ' + label);
      return null;
    }

    return exp;
  }

  // Make a substitution of variables. The result is put in "destination".
  makesubstitution(original: Expression, substmap: {[label: string]: Expression}): Expression {
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

  getproofnumbers(label: string, proof: string): number[] {
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
  verifyassertionref(thlabel: string, reflabel: string, stack: Expression[]): Expression[] {
    const assertion: Assertion = this.assertions[reflabel];

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
      const hypothesis: Hypothesis = this.hypotheses[assertion.hypotheses[i]];

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
        const dest: Expression = this.makesubstitution(hypothesis.first, substitutions);
        if (!arraysequal(dest, stack[base + i])) {
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
        if (this.variables.has(exp1[nExp1])) {
          exp1vars.push(exp1[nExp1]);
        }
      }

      const exp2vars: string[] = [];
      for (let nExp2 = 0; nExp2 < exp2.length; ++nExp2) {
        if (this.variables.has(exp2[nExp2])) {
          exp2vars.push(exp2[nExp2]);
        }
      }

      for (let nExp1 = 0; nExp1 < exp1vars.length; ++nExp1) {
        for (let nExp2 = 0; nExp2 < exp2vars.length; ++nExp2) {
          if (!this.isdvr(exp1vars[nExp1], exp2vars[nExp2])) {
            console.error('In proof of theorem ' + thlabel + ' disjoint variable restriction violated');
            return null;
          }
        }
      }
    }

    // Done verification of this step. Insert new statement onto stack.
    const result: Expression = this.makesubstitution(assertion.expression, substitutions);
    stack.push(result);
    return stack;
  }

  // Verify a regular proof. The "proof" argument should be a non-empty sequence
  // of valid labels. Return true iff the proof is correct.
  verifyregularproof(label: string, theorem: Assertion, proof: string[]): boolean {
    let stack: Expression[] = [];
    for (let n = 0; n < proof.length; ++n) {
      // If step is a hypothesis, just push it onto the stack.
      const hyp: Hypothesis = this.hypotheses[proof[n]];
      if (hyp) {
        stack.push(hyp.first);
        continue;
      }

      // It must be an axiom or theorem
      stack = this.verifyassertionref(label, proof[n], stack);
      if (stack === null) {
        return false;
      }
    }

    if (stack.length !== 1) {
      console.error('Proof of theorem ' + label + ' does not end with only one item on the stack');
      return false;
    }

    if (!arraysequal(stack[0], theorem.expression)) {
      console.error('Proof of theorem ' + label + ' proves wrong statement');
      return false;
    }

    return true;
  }

  // Verify a compressed proof
  verifycompressedproof(label: string, theorem: Assertion, labels: string[], proofnumbers: number[]): boolean {
    let stack: Expression[] = [];

    const mandhypt: number = theorem.hypotheses.length;
    const labelt = mandhypt + labels.length;

    const savedsteps: Expression[] = [];
    for (let n = 0; n < proofnumbers.length; ++n) {
      // Save the last proof step if 0
      if (proofnumbers[n] === 0) {
        savedsteps.push(stack[stack.length - 1]);
        continue;
      }

      // If step is a mandatory hypothesis, just push it onto the stack.
      if (proofnumbers[n] <= mandhypt) {
        stack.push(this.hypotheses[theorem.hypotheses[proofnumbers[n] - 1]].first);
      } else if (proofnumbers[n] <= labelt) {
        const proofstep: string = labels[proofnumbers[n] - mandhypt - 1];

        // If step is a (non-mandatory) hypothesis,
        // just push it onto the stack.
        const hyp: Hypothesis = this.hypotheses[proofstep];
        if (hyp) {
          stack.push(hyp.first);
          continue;
        }

        // It must be an axiom or theorem
        stack = this.verifyassertionref(label, proofstep, stack);
        if (stack === null) {
          return false;
        }
      } else { // Must refer to saved step
        if (proofnumbers[n] > labelt + savedsteps.length) {
          console.error('Number in compressed proof of ' + label + ' is too high');
          return false;
        }

        stack.push(savedsteps[proofnumbers[n] - labelt - 1]);
      }
    }

    if (stack.length !== 1) {
      console.error('Proof of theorem ' + label + ' does not end with only one item on the stack');
      return false;
    }

    if (!arraysequal(stack[0], theorem.expression)) {
      console.error('Proof of theorem ' + label + ' proves wrong statement');
      return false;
    }

    return true;
  }

  // Parse $p statement. Return true iff okay.
  parsep(label: string): boolean {
    const newtheorem: Expression = this.readexpression('p', label, '$=');
    if (!newtheorem) {
      return false;
    }

    const assertion: Assertion = this.constructassertion(label, newtheorem);

    // Now for the proof

    if (!this.tokens.length) {
      console.error('Unfinished $p statement ' + label);
      return false;
    }

    if (this.tokens[0] === '(') {
      // Compressed proof
      this.tokens.shift();

      // Get labels

      const labels: string[] = [];

      while (this.tokens.length) {
        const token: string = this.tokens[0];
        if (token === ')') {
          break;
        }

        this.tokens.shift();
        labels.push(token);
        if (token === label) {
          console.error('Proof of theorem ' + label + ' refers to itself');
          return false;
        } else if (assertion.hypotheses.find((value) => value === token) !== undefined) {
          console.error('Compressed proof of theorem ' + label + ' has mandatory hypothesis ' + token + ' in label list');
          return false;
        } else if (!this.assertions[token] && !this.isactivehyp(token)) {
          console.error('Proof of theorem ' + label + ' refers to ' + token + ' which is not an active statement');
          return false;
        }
      }

      if (!this.tokens.length) {
        console.error('Unfinished $p statement ' + label);
        return false;
      }

      this.tokens.shift(); // Discard ) token

      // Get proof steps

      let proof: string = '';
      while (this.tokens.length) {
        const token = this.tokens[0];

        if (token === '$.') {
          break;
        }

        this.tokens.shift();

        proof += token;
        if (!this.containsonlyupperorq(token)) {
          console.error('Bogus character found in compressed proof of ' + label);
          return false;
        }
      }

      if (!this.tokens.length) {
        console.error('Unfinished $p statement ' + label);
        return false;
      }

      if (!proof.length) {
        console.error('Theorem ' + label + ' has no proof');
        return false;
      }

      this.tokens.shift(); // Discard $. token

      if (proof.indexOf('?') !==  -1) {
        console.error('Warning: Proof of theorem ' + label + ' is incomplete');
        return true; // Continue processing file
      }

      const proofnumbers: number[] = this.getproofnumbers(label, proof);
      if (!proofnumbers) {
        return false;
      }

      const okay: boolean = this.verifycompressedproof(label, assertion, labels, proofnumbers);
      if (!okay) {
        return false;
      }
    } else {
      // Regular (uncompressed proof)
      const proof: string[] = [];
      let incomplete = false;
      while (this.tokens.length) {
        const token: string = this.tokens[0];

        if (token === '$.') {
          break;
        }

        this.tokens.shift();
        proof.push(token);
        if (token === '?') {
          incomplete = true;
        } else if (token === label) {
          console.error('Proof of theorem ' + label + ' refers to itself');
          return false;
        } else if (!this.assertions[token] && !this.isactivehyp(token)) {
          console.error('Proof of theorem ' + label + ' refers to ' + token + ' which is not an active statement');
          return false;
        }
      }

      if (!this.tokens.length) {
        console.error('Unfinished $p statement ' + label);
        return false;
      }

      if (!proof.length) {
        console.error('Theorem ' + label + ' has no proof');
        return false;
      }

      this.tokens.shift(); // Discard $. token

      if (incomplete) {
        console.error('Warning: Proof of theorem ' + label + ' is incomplete');
        return true; // Continue processing file
      }

      const okay: boolean = this.verifyregularproof(label, assertion, proof);
      if (!okay) {
        return false;
      }
    }

    return true;
  }

  parsee(label: string): boolean {
    const newhyp: Expression = this.readexpression('e', label, '$.');
    if (!newhyp) {
      return false;
    }

    // Create new essential hypothesis
    this.hypotheses[label] = {
      first: newhyp,
      second: false
    };

    this.scopes[this.scopes.length - 1].activehyp.push(label);
    return true;
  }

  // Parse $a statement. Return true iff okay.
  parsea(label: string): boolean {
    const newaxiom: Expression = this.readexpression('a', label, '$.');
    if (!newaxiom) {
      return false;
    }

    this.constructassertion(label, newaxiom);

    return true;
  }

  // Parse $f statement. Return true iff okay.
  parsef(label: string): boolean {
    if (!this.tokens.length) {
      console.error('Unfinished $f statement' + label);
      return false;
    }

    const type: string = this.tokens[0];

    if (this.constants.find((value) => value === type) === undefined) {
      console.error('First symbol in $f statement ' + label + ' is ' + type + ' which is not a constant');
      return false;
    }

    this.tokens.shift();

    if (!this.tokens.length) {
      console.error('Unfinished $f statement' + label);
      return false;
    }

    const variable: string = this.tokens[0];
    if (!this.isactivevariable(variable)) {
      console.error('Second symbol in $f statement ' + label + ' is ' + variable + ' which is not an active variable');
      return false;
    }
    if (this.getfloatinghyp(variable).length) {
      console.error('The variable ' + variable + ' appears in a second $f statement ' + label);
      return false;
    }

    this.tokens.shift();

    if (!this.tokens.length) {
      console.error('Unfinished $f statement' + label);
      return false;
    }

    if (this.tokens[0] !== '$.') {
      console.error('Expected end of $f statement ' + label + ' but found ' + this.tokens[0]);
      return false;
    }

    this.tokens.shift(); // Discard $. token

    // Create new floating hypothesis
    const newhyp: Expression = [];
    newhyp.push(type);
    newhyp.push(variable);
    this.hypotheses[label] = {
      first: newhyp,
      second: true
    };
    this.scopes[this.scopes.length - 1].activehyp.push(label);
    this.scopes[this.scopes.length - 1].floatinghyp[variable] = label;
    return true;
  }

  // Parse labeled statement. Return true iff okay.
  parselabel(label: string): boolean {
    if (this.constants.find((value) => value === label) !== undefined) {
      console.error('Attempt to reuse constant ' + label + ' as a label');
      return false;
    }

    if (this.variables.has(label)) {
      console.error('Attempt to reuse variable ' + label + ' as a label');
      return false;
    }

    if (this.labelused(label)) {
      console.error('Attempt to reuse label ' + label);
      return false;
    }

    if (!this.tokens.length) {
      console.error('Unfinished labeled statement');
      return false;
    }

    const type: string = this.tokens.shift();

    let okay = true;
    if (type === '$p') {
      okay = this.parsep(label);
      ++this.nProofCount;
    } else if (type === '$e') {
      okay = this.parsee(label);
    } else if (type === '$a') {
      okay = this.parsea(label);
    } else if (type === '$f') {
      okay = this.parsef(label);
    } else {
      console.error('Unexpected token ' + type + ' encountered');
      return false;
    }

    return okay;
  }

  parsed(): boolean {
    const dvars: Set<string> = new Set<string>();

    while (this.tokens.length) {
      const token: string = this.tokens[0];
      if (token === '$.') {
        break;
      }

      this.tokens.shift();

      if (!this.isactivevariable(token)) {
        console.error('Token ' + token + ' is not an active variable, ' + 'but was found in a $d statement');
        return false;
      }

      if (dvars.has(token)) {
        console.error('$d statement mentions ' + token + ' twice');
        return false;
      }

      dvars.add(token);
    }

    if (!this.tokens.length) {
      console.error('Unterminated $d statement');
      return false;
    }

    if (dvars.size < 2) {
      console.error('Not enough items in $d statement');
      return false;
    }

    // Record it
    this.scopes[this.scopes.length - 1].disjvars.push(dvars);

    this.tokens.shift(); // Discard $. token

    return true;
  }

  // Parse $c statement. Return true iff okay.
  parsec(): boolean {
    if (this.scopes.length > 1) {
      console.error('$c statement occurs in inner block');
      return false;
    }

    let listempty = true;
    while (this.tokens.length) {
      const token = this.tokens[0];

      if (token === '$.') {
        break;
      }

      this.tokens.shift();
      listempty = false;

      if (!this.ismathsymboltoken(token)) {
        console.error('Attempt to declare ' + token + ' as a constant');
        return false;
      }
      if (this.variables.has(token)) {
        console.error('Attempt to redeclare variable ' + token + ' as a constant');
        return false;
      }
      if (this.labelused(token)) {
        console.error('Attempt to reuse label ' + token + ' as a constant');
        return false;
      }
      if (this.constants.find((value) => value === token) !== undefined) {
        console.error('Attempt to redeclare constant ' + token);
        return false;
      }
      this.constants.push(token);
    }

    if (!this.tokens.length) {
      console.error('Unterminated $c statement');
      return false;
    }

    if (listempty) {
      console.error('Unterminated $c statement');
      return false;
    }

    this.tokens.shift(); // Discard $. token

    return true;
  }

  // Parse $v statement. Return true iff okay.
  parsev(): boolean {
    let listempty = true;
    while (this.tokens.length) {
      const token: string = this.tokens[0];

      if (token === '$.') {
        break;
      }

      this.tokens.shift();
      listempty = false;

      if (!this.ismathsymboltoken(token)) {
        console.error('Attempt to declare ' + token + ' as a variable');
        return false;
      }
      if (this.constants.find((value) => value === token) !== undefined) {
        console.error('Attempt to redeclare constant ' + token + ' as a variable');
        return false;
      }
      if (this.labelused(token)) {
        console.error('Attempt to reuse label ' + token + ' as a variable');
        return false;
      }
      if (this.isactivevariable(token)) {
        console.error('Attempt to redeclare active variable ' + token);
        return false;
      }
      this.variables.add(token);
      this.scopes[this.scopes.length - 1].activevariables.add(token);
    }

    if (!this.tokens.length) {
      console.error('Unterminated $v statement');
      return false;
    }

    if (listempty) {
      console.error('Empty $v statement');
      return false;
    }

    this.tokens.shift(); // Discard $. token

    return true;
  }

  checkmm(): boolean {

    this.scopes.push(new Scope());

    while (this.tokens.length) {
      const token: string = this.tokens.shift();

      let okay = true;

      if (this.islabeltoken(token)) {
        okay = this.parselabel(token);
      } else if (token === '$d') {
        okay = this.parsed();
      } else if (token === '${') {
        this.scopes.push(new Scope());
      } else if (token === '$}') {
        this.scopes.pop();
        if (!this.scopes.length) {
          console.error('$} without corresponding ${');
          return false;
        }
      } else if (token === '$c') {
        okay = this.parsec();
      } else if (token === '$v') {
        okay = this.parsev();
      } else {
        console.error('Unexpected token ' + token + ' encountered');
        return false;
      }
      if (!okay) {
        return false;
      }

      if (this.nProofCount >= this.nProofLimit) {
        console.log('Proof limit reached');
        console.log('Successfully verified ' + this.nProofCount + ' proofs');
        return true;
      }
    }

    if (this.scopes.length > 1) {
      console.error('${ without corresponding $}');
      return false;
    }

    console.log('Successfully verified ' + this.nProofCount + ' proofs\n');
    return true;
  }
}

const EXIT_FAILURE = 1;

function main(argv: string[]): number {

  const checkmm: CheckMM = new CheckMM();

  if (argv.length === 3) {
    const newProofLimit = parseInt(argv[2], 10);
    if (newProofLimit) {
      checkmm.nProofLimit = newProofLimit;
    }  else {
      console.error('Invalid proof limit' + argv[2]);
    }
    argv.pop();
  }

  if (argv.length !== 2) {
    console.error('Syntax: node checkmm.js <filename> [<proof-limit>]');
    return EXIT_FAILURE;
  }

  checkmm.setState({});

  let okay: boolean = checkmm.readtokens(argv[1]);
  if (!okay) {
    return EXIT_FAILURE;
  }

  okay = checkmm.checkmm();
  return okay ? 0 : EXIT_FAILURE;
}

// Are we being run as a program or a library?
if (process.argv.length >= 2 && path.basename(process.argv[1]) === path.basename(__filename)) {
  // We are being run as a program
  process.exitCode = main(process.argv.slice(1));
}

