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

export const std = {
  isupper: (s: string): boolean => {
    if ( /[^A-Z]/.test(s)) {
      return false;
    } else {
      return true;
    }
  },
  isalnum: (s: string): boolean => {
    if ( /[^a-zA-Z0-9]/.test(s)) {
      return false;
    } else {
      return true;
    }
  }
};

let tokens: string[] = [];

const constants: string[] = [];

type Expression = string[];

// The first parameter is the statement of the hypothesis, the second is
// true iff the hypothesis is floating.
class Hypothesis {
  first: Expression;
  second: boolean;
}

let hypotheses: {[token: string]: Hypothesis} = {};

const variables: {[token: string]: null} = {};

// An axiom or a theorem.
class Assertion {
    // Hypotheses of this axiom or theorem.
    hypotheses: string[] = [];
    disjvars: {[token: string]: [string, string]} = {};

    // Statement of axiom or theorem.
    expression: Expression = [];
}

let assertions: {[token: string]: Assertion} = {};

class Scope {
  activevariables: {[token: string]: null};
  // Labels of active hypotheses
  activehyp: string[] = [];
  disjvars: {[token: string]: void}[] = [];
  // Map from variable to label of active floating hypothesis
  floatinghyp: {[token: string]: string} = {};
}

let scopes: Scope[] = [];

interface TestValues {
  tokens?: string[];
  hypotheses?: {[token: string]: Hypothesis};
  assertions?: {[token: string]: Assertion};
  scopes?: Scope[];
}

export function initTestValues(values: TestValues) {
  ({tokens, hypotheses, assertions, scopes} = {
    tokens: [],
    hypotheses: {},
    assertions: {},
    scopes: [],
    ...values
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
    if (scopes[nScope].activevariables[str] !== undefined) {
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
      if (disjvar[var1] !== undefined
      &&  disjvar[var2] !== undefined) {
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

export function nexttoken(input: fs.ReadStream): string {
    let ch: string = null;
    let token: string = '';

    // Skip whitespace
    while (true) {
      ch = input.read(1) as string;
      if (ch === null || !ismmws(ch)) {
        break;
      }
    }

    if (ch !== null) {
      input.unshift(ch);
    }

    // Get token
    while (true) {
      ch = input.read(1) as string;

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

const names: {[name: string]: null} = {};

export function readtokens(filename: string): boolean {
  const alreadyencountered: boolean = (names[filename] === null);
  if (alreadyencountered) {
    return true;
  }

  names[filename] = null;

  const fin = fs.createReadStream(filename, {encoding: 'utf8'});

  if (!fin) {
    console.error('Could not open ' + filename);
    return false;
  }

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
        console.log('Characters $( found in a comment');
        return false;
      }
      if (token.indexOf('$)') !== -1) {
        console.log('Characters $) found in a comment');
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
          console.log('Filename ' + token + ' contains a $');
          return false;
        }
        newfilename = token;
        continue;
      } else {
        if (token !== '$]') {
          console.log('Didn\'t find closing file inclusion delimiter');
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

