"use strict";
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
var __extends = (this && this.__extends) || (function () {
    var extendStatics = function (d, b) {
        extendStatics = Object.setPrototypeOf ||
            ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
            function (d, b) { for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p]; };
        return extendStatics(d, b);
    };
    return function (d, b) {
        extendStatics(d, b);
        function __() { this.constructor = d; }
        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
    };
})();
var __assign = (this && this.__assign) || function () {
    __assign = Object.assign || function(t) {
        for (var s, i = 1, n = arguments.length; i < n; i++) {
            s = arguments[i];
            for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p))
                t[p] = s[p];
        }
        return t;
    };
    return __assign.apply(this, arguments);
};
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (Object.hasOwnProperty.call(mod, k)) result[k] = mod[k];
    result["default"] = mod;
    return result;
};
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
var fs = __importStar(require("fs"));
var path = __importStar(require("path"));
var lodash_1 = __importDefault(require("lodash"));
// checkmm uses a little bit of C++'s Standard Template Library.  Simulate it.
var std;
(function (std) {
    function isupper(s) {
        if (/[^A-Z]/.test(s)) {
            return false;
        }
        else {
            return true;
        }
    }
    std.isupper = isupper;
    function isalnum(s) {
        if (/[^a-zA-Z0-9]/.test(s)) {
            return false;
        }
        else {
            return true;
        }
    }
    std.isalnum = isalnum;
    function set_intersection(s1, s2) {
        var s3 = new Set();
        s1.forEach(function (value) {
            if (s2.has(value)) {
                s3.add(value);
            }
        });
        return s3;
    }
    std.set_intersection = set_intersection;
    var Pair = /** @class */ (function () {
        function Pair() {
        }
        return Pair;
    }());
    std.Pair = Pair;
})(std = exports.std || (exports.std = {}));
// Simple function for comparing arrays (in C++ STL handles this automatically)
function arraysequal(arr1, arr2) {
    if (arr1.length !== arr2.length) {
        return false;
    }
    for (var n = 0; n < arr1.length; ++n) {
        if (arr1[n] !== arr2[n]) {
            return false;
        }
    }
    return true;
}
// An axiom or a theorem.
var Assertion = /** @class */ (function () {
    function Assertion() {
        // Hypotheses of this axiom or theorem.
        this.hypotheses = [];
        this.disjvars = [];
        // Statement of axiom or theorem.
        this.expression = [];
    }
    return Assertion;
}());
exports.Assertion = Assertion;
var Scope = /** @class */ (function () {
    function Scope() {
        this.activevariables = new Set();
        // Labels of active hypotheses
        this.activehyp = [];
        this.disjvars = [];
        // Map from variable to label of active floating hypothesis
        this.floatinghyp = {};
    }
    return Scope;
}());
exports.Scope = Scope;
var State = /** @class */ (function () {
    function State() {
        this.tokens = [];
        this.constants = [];
        this.hypotheses = {};
        this.variables = new Set();
        this.assertions = {};
        this.scopes = [];
        this.nProofCount = 0;
        this.nProofLimit = Number.MAX_SAFE_INTEGER;
        this.mmFileNames = new Set();
    }
    return State;
}());
exports.State = State;
var CheckMM = /** @class */ (function (_super) {
    __extends(CheckMM, _super);
    function CheckMM() {
        return _super !== null && _super.apply(this, arguments) || this;
    }
    CheckMM.prototype.setState = function (partialState) {
        var _this = this;
        var defaultState = new State();
        var state = __assign({}, defaultState, partialState);
        Object.keys(state).forEach(function (key) {
            _this[key] = state[key];
        });
    };
    CheckMM.prototype.getState = function () {
        var _this = this;
        var state = new State();
        Object.keys(state).forEach(function (key) {
            state[key] = _this[key];
        });
        return lodash_1.default.cloneDeep(state);
    };
    // Determine if a string is used as a label
    CheckMM.prototype.labelused = function (label) {
        return (this.hypotheses[label] || this.assertions[label]) ? true : false;
    };
    // Find active floating hypothesis corresponding to variable, or empty string
    // if there isn't one.
    CheckMM.prototype.getfloatinghyp = function (variable) {
        for (var nScope = 0; nScope < this.scopes.length; ++nScope) {
            var loc = this.scopes[nScope].floatinghyp[variable];
            if (loc !== undefined) {
                return loc;
            }
        }
        return '';
    };
    CheckMM.prototype.isactivevariable = function (str) {
        for (var nScope = 0; nScope < this.scopes.length; ++nScope) {
            if (this.scopes[nScope].activevariables.has(str)) {
                return true;
            }
        }
        return false;
    };
    CheckMM.prototype.isactivehyp = function (str) {
        for (var nScope = 0; nScope < this.scopes.length; ++nScope) {
            if (this.scopes[nScope].activehyp.find(function (value) { return value === str; }) !== undefined) {
                return true;
            }
        }
        return false;
    };
    // Determine if there is an active disjoint variable restriction on
    // two different variables.
    CheckMM.prototype.isdvr = function (var1, var2) {
        if (var1 === var2) {
            return false;
        }
        for (var nScope = 0; nScope < this.scopes.length; ++nScope) {
            var scope = this.scopes[nScope];
            for (var nDisjvar = 0; nDisjvar !== scope.disjvars.length; ++nDisjvar) {
                var disjvar = scope.disjvars[nDisjvar];
                if (disjvar.has(var1)
                    && disjvar.has(var2)) {
                    return true;
                }
            }
        }
        return false;
    };
    // Determine if a character is white space in Metamath.
    CheckMM.prototype.ismmws = function (ch) {
        // This doesn't include \v ("vertical tab"), as the spec omits it.
        return ch === ' ' || ch === '\n' || ch === '\t' || ch === '\f' || ch === '\r';
    };
    // Determine if a token is a label token.
    CheckMM.prototype.islabeltoken = function (token) {
        for (var nCh = 0; nCh < token.length; ++nCh) {
            var ch = token[nCh];
            if (!(std.isalnum(ch) || ch === '.' || ch === '-' || ch === '_')) {
                return false;
            }
        }
        return true;
    };
    // Determine if a token is a math symbol token.
    CheckMM.prototype.ismathsymboltoken = function (token) {
        return token.indexOf('$') === -1;
    };
    // Determine if a token consists solely of upper-case letters or question marks
    CheckMM.prototype.containsonlyupperorq = function (token) {
        for (var nCh = 0; nCh < token.length; ++nCh) {
            var ch = token[nCh];
            if (!std.isupper(ch) && ch !== '?') {
                return false;
            }
        }
        return true;
    };
    CheckMM.prototype.nexttoken = function (input) {
        var ch = null;
        var token = '';
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
                return { token: '', input: input };
            }
            token += ch;
        }
        return { token: token, input: input };
    };
    CheckMM.prototype.readtokens = function (filename) {
        var _a;
        var alreadyencountered = this.mmFileNames.has(filename);
        if (alreadyencountered) {
            return true;
        }
        this.mmFileNames.add(filename);
        var input = fs.readFileSync(filename, { encoding: 'utf8' });
        var incomment = false;
        var infileinclusion = false;
        var newfilename = '';
        var token = '';
        while (true) {
            (_a = this.nexttoken(input), token = _a.token, input = _a.input);
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
                }
                else {
                    if (token !== '$]') {
                        console.error('Didn\'t find closing file inclusion delimiter');
                        return false;
                    }
                    var okay = this.readtokens(newfilename);
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
    };
    // Construct an Assertion from an Expression. That is, determine the
    // mandatory hypotheses and disjoint variable restrictions.
    // The Assertion is inserted into the assertions collection,
    // and is returned.
    CheckMM.prototype.constructassertion = function (label, exp) {
        var assertion = new Assertion();
        assertion.expression = exp;
        var varsused = new Set();
        // Determine variables used and find mandatory hypotheses
        for (var n = 0; n < exp.length; ++n) {
            var variable = exp[n];
            if (this.variables.has(variable)) {
                varsused.add(variable);
            }
        }
        for (var nScope = this.scopes.length - 1; nScope >= 0; --nScope) {
            var hypvec = this.scopes[nScope].activehyp;
            for (var n = hypvec.length - 1; n >= 0; --n) {
                var hyp = this.hypotheses[hypvec[n]];
                if (hyp.second && varsused.has(hyp.first[1])) {
                    // Mandatory floating hypothesis
                    assertion.hypotheses.unshift(hypvec[n]);
                }
                else if (!hyp.second) {
                    // Essential hypothesis
                    assertion.hypotheses.unshift(hypvec[n]);
                    for (var nExpression = 0; nExpression < hyp.first.length; ++nExpression) {
                        if (this.variables.has(hyp.first[nExpression])) {
                            varsused.add(hyp.first[nExpression]);
                        }
                    }
                }
            }
        }
        // Determine mandatory disjoint variable restrictions
        for (var nScope = 0; nScope < this.scopes.length; ++nScope) {
            var disjvars = this.scopes[nScope].disjvars;
            var _loop_1 = function (nDisjvars) {
                var dset = [];
                std.set_intersection(disjvars[nDisjvars], varsused).forEach(function (value) {
                    dset.push(value);
                });
                for (var n = 0; n < dset.length; ++n) {
                    for (var n2 = n + 1; n2 < dset.length; ++n2) {
                        assertion.disjvars.push([dset[n], dset[n2]]);
                    }
                }
            };
            for (var nDisjvars = 0; nDisjvars < disjvars.length; ++nDisjvars) {
                _loop_1(nDisjvars);
            }
        }
        this.assertions[label] = assertion;
        return assertion;
    };
    // Read an expression from the token stream.
    CheckMM.prototype.readexpression = function (stattype, label, terminator) {
        var exp = [];
        if (!this.tokens.length) {
            console.error('Unfinished $' + stattype + ' statement ' + label);
            return null;
        }
        var type = this.tokens[0];
        if (this.constants.find(function (value) { return type === value; }) === undefined) {
            console.error('First symbol in $' + stattype + ' statement ' + label + ' is ' + type + ' which is not a constant');
            return null;
        }
        this.tokens.shift();
        exp.push(type);
        var _loop_2 = function () {
            var token = this_1.tokens.shift();
            if (token === terminator) {
                return "break";
            }
            if (this_1.constants.find(function (value) { return value === token; }) === undefined
                && this_1.getfloatinghyp(token).length === 0) {
                console.error('In $' + stattype + ' statement ' + label
                    + ' token ' + token
                    + ' found which is not a constant or variable in an'
                    + ' active $f statement');
                return { value: null };
            }
            exp.push(token);
        };
        var this_1 = this;
        while (this.tokens.length) {
            var state_1 = _loop_2();
            if (typeof state_1 === "object")
                return state_1.value;
            if (state_1 === "break")
                break;
        }
        if (!this.tokens.length) {
            console.error('Unfinished $' + stattype + ' statement ' + label);
            return null;
        }
        return exp;
    };
    // Make a substitution of variables. The result is put in "destination".
    CheckMM.prototype.makesubstitution = function (original, substmap) {
        var destination = [];
        for (var n = 0; n < original.length; ++n) {
            var substitution = substmap[original[n]];
            if (substitution === undefined) {
                // Constant
                destination.push(original[n]);
            }
            else {
                destination = destination.concat(substitution);
            }
        }
        return destination;
    };
    CheckMM.prototype.getproofnumbers = function (label, proof) {
        var proofnumbers = [];
        var num = 0;
        var justgotnum = false;
        for (var n = 0; n < proof.length; ++n) {
            if (proof[n] <= 'T') {
                var addval = proof.charCodeAt(n) - ('A'.charCodeAt(0) - 1);
                if (num > Number.MAX_SAFE_INTEGER / 20 || 20 * num > Number.MAX_SAFE_INTEGER - addval) {
                    console.error('Overflow computing numbers in compressed proof of ' + label);
                    return null;
                }
                proofnumbers.push((20 * num) + addval);
                num = 0;
                justgotnum = true;
            }
            else if (proof[n] <= 'Y') {
                var addval = proof.charCodeAt(n) - 'T'.charCodeAt(0);
                if (num > Number.MAX_SAFE_INTEGER / 5 || 5 * num > Number.MAX_SAFE_INTEGER - addval) {
                    console.error('Overflow computing numbers in compressed proof of ' + label);
                    return null;
                }
                num = (5 * num) + addval;
                justgotnum = false;
            }
            else { // It must be Z
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
    };
    // Subroutine for proof verification. Verify a proof step referencing an
    // assertion (i.e., not a hypothesis).
    CheckMM.prototype.verifyassertionref = function (thlabel, reflabel, stack) {
        var assertion = this.assertions[reflabel];
        if (!assertion) {
            console.error('In proof of theorem ' + thlabel + ' assertion ' + reflabel + ' is undefined');
            return null;
        }
        if (stack.length < assertion.hypotheses.length) {
            console.error('In proof of theorem ' + thlabel + ' not enough items found on stack');
            return null;
        }
        var base = stack.length - assertion.hypotheses.length;
        var substitutions = {};
        // Determine substitutions and check that we can unify
        for (var i = 0; i < assertion.hypotheses.length; ++i) {
            var hypothesis = this.hypotheses[assertion.hypotheses[i]];
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
                var subst = stack[base + i].slice(1);
                substitutions[hypothesis.first[1]] = subst;
            }
            else {
                // Essential hypothesis
                var dest = this.makesubstitution(hypothesis.first, substitutions);
                if (!arraysequal(dest, stack[base + i])) {
                    console.error('In proof of theorem ' + thlabel + ' unification failed');
                    return null;
                }
            }
        }
        // Remove hypotheses from stack
        stack = stack.slice(0, base);
        // Verify disjoint variable conditions
        for (var nDisjvar = 0; nDisjvar < assertion.disjvars.length; ++nDisjvar) {
            var exp1 = substitutions[assertion.disjvars[nDisjvar][0]];
            var exp2 = substitutions[assertion.disjvars[nDisjvar][1]];
            var exp1vars = [];
            for (var nExp1 = 0; nExp1 < exp1.length; ++nExp1) {
                if (this.variables.has(exp1[nExp1])) {
                    exp1vars.push(exp1[nExp1]);
                }
            }
            var exp2vars = [];
            for (var nExp2 = 0; nExp2 < exp2.length; ++nExp2) {
                if (this.variables.has(exp2[nExp2])) {
                    exp2vars.push(exp2[nExp2]);
                }
            }
            for (var nExp1 = 0; nExp1 < exp1vars.length; ++nExp1) {
                for (var nExp2 = 0; nExp2 < exp2vars.length; ++nExp2) {
                    if (!this.isdvr(exp1vars[nExp1], exp2vars[nExp2])) {
                        console.error('In proof of theorem ' + thlabel + ' disjoint variable restriction violated');
                        return null;
                    }
                }
            }
        }
        // Done verification of this step. Insert new statement onto stack.
        var result = this.makesubstitution(assertion.expression, substitutions);
        stack.push(result);
        return stack;
    };
    // Verify a regular proof. The "proof" argument should be a non-empty sequence
    // of valid labels. Return true iff the proof is correct.
    CheckMM.prototype.verifyregularproof = function (label, theorem, proof) {
        var stack = [];
        for (var n = 0; n < proof.length; ++n) {
            // If step is a hypothesis, just push it onto the stack.
            var hyp = this.hypotheses[proof[n]];
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
    };
    // Verify a compressed proof
    CheckMM.prototype.verifycompressedproof = function (label, theorem, labels, proofnumbers) {
        var stack = [];
        var mandhypt = theorem.hypotheses.length;
        var labelt = mandhypt + labels.length;
        var savedsteps = [];
        for (var n = 0; n < proofnumbers.length; ++n) {
            // Save the last proof step if 0
            if (proofnumbers[n] === 0) {
                savedsteps.push(stack[stack.length - 1]);
                continue;
            }
            // If step is a mandatory hypothesis, just push it onto the stack.
            if (proofnumbers[n] <= mandhypt) {
                stack.push(this.hypotheses[theorem.hypotheses[proofnumbers[n] - 1]].first);
            }
            else if (proofnumbers[n] <= labelt) {
                var proofstep = labels[proofnumbers[n] - mandhypt - 1];
                // If step is a (non-mandatory) hypothesis,
                // just push it onto the stack.
                var hyp = this.hypotheses[proofstep];
                if (hyp) {
                    stack.push(hyp.first);
                    continue;
                }
                // It must be an axiom or theorem
                stack = this.verifyassertionref(label, proofstep, stack);
                if (stack === null) {
                    return false;
                }
            }
            else { // Must refer to saved step
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
    };
    // Parse $p statement. Return true iff okay.
    CheckMM.prototype.parsep = function (label) {
        var newtheorem = this.readexpression('p', label, '$=');
        if (!newtheorem) {
            return false;
        }
        var assertion = this.constructassertion(label, newtheorem);
        // Now for the proof
        if (!this.tokens.length) {
            console.error('Unfinished $p statement ' + label);
            return false;
        }
        if (this.tokens[0] === '(') {
            // Compressed proof
            this.tokens.shift();
            // Get labels
            var labels = [];
            var _loop_3 = function () {
                var token = this_2.tokens[0];
                if (token === ')') {
                    return "break";
                }
                this_2.tokens.shift();
                labels.push(token);
                if (token === label) {
                    console.error('Proof of theorem ' + label + ' refers to itself');
                    return { value: false };
                }
                else if (assertion.hypotheses.find(function (value) { return value === token; }) !== undefined) {
                    console.error('Compressed proof of theorem ' + label + ' has mandatory hypothesis ' + token + ' in label list');
                    return { value: false };
                }
                else if (!this_2.assertions[token] && !this_2.isactivehyp(token)) {
                    console.error('Proof of theorem ' + label + ' refers to ' + token + ' which is not an active statement');
                    return { value: false };
                }
            };
            var this_2 = this;
            while (this.tokens.length) {
                var state_2 = _loop_3();
                if (typeof state_2 === "object")
                    return state_2.value;
                if (state_2 === "break")
                    break;
            }
            if (!this.tokens.length) {
                console.error('Unfinished $p statement ' + label);
                return false;
            }
            this.tokens.shift(); // Discard ) token
            // Get proof steps
            var proof = '';
            while (this.tokens.length) {
                var token = this.tokens[0];
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
            if (proof.indexOf('?') !== -1) {
                console.error('Warning: Proof of theorem ' + label + ' is incomplete');
                return true; // Continue processing file
            }
            var proofnumbers = this.getproofnumbers(label, proof);
            if (!proofnumbers) {
                return false;
            }
            var okay = this.verifycompressedproof(label, assertion, labels, proofnumbers);
            if (!okay) {
                return false;
            }
        }
        else {
            // Regular (uncompressed proof)
            var proof = [];
            var incomplete = false;
            while (this.tokens.length) {
                var token = this.tokens[0];
                if (token === '$.') {
                    break;
                }
                this.tokens.shift();
                proof.push(token);
                if (token === '?') {
                    incomplete = true;
                }
                else if (token === label) {
                    console.error('Proof of theorem ' + label + ' refers to itself');
                    return false;
                }
                else if (!this.assertions[token] && !this.isactivehyp(token)) {
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
            var okay = this.verifyregularproof(label, assertion, proof);
            if (!okay) {
                return false;
            }
        }
        return true;
    };
    CheckMM.prototype.parsee = function (label) {
        var newhyp = this.readexpression('e', label, '$.');
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
    };
    // Parse $a statement. Return true iff okay.
    CheckMM.prototype.parsea = function (label) {
        var newaxiom = this.readexpression('a', label, '$.');
        if (!newaxiom) {
            return false;
        }
        this.constructassertion(label, newaxiom);
        return true;
    };
    // Parse $f statement. Return true iff okay.
    CheckMM.prototype.parsef = function (label) {
        if (!this.tokens.length) {
            console.error('Unfinished $f statement' + label);
            return false;
        }
        var type = this.tokens[0];
        if (this.constants.find(function (value) { return value === type; }) === undefined) {
            console.error('First symbol in $f statement ' + label + ' is ' + type + ' which is not a constant');
            return false;
        }
        this.tokens.shift();
        if (!this.tokens.length) {
            console.error('Unfinished $f statement' + label);
            return false;
        }
        var variable = this.tokens[0];
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
        var newhyp = [];
        newhyp.push(type);
        newhyp.push(variable);
        this.hypotheses[label] = {
            first: newhyp,
            second: true
        };
        this.scopes[this.scopes.length - 1].activehyp.push(label);
        this.scopes[this.scopes.length - 1].floatinghyp[variable] = label;
        return true;
    };
    // Parse labeled statement. Return true iff okay.
    CheckMM.prototype.parselabel = function (label) {
        if (this.constants.find(function (value) { return value === label; }) !== undefined) {
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
        var type = this.tokens.shift();
        var okay = true;
        if (type === '$p') {
            okay = this.parsep(label);
            ++this.nProofCount;
        }
        else if (type === '$e') {
            okay = this.parsee(label);
        }
        else if (type === '$a') {
            okay = this.parsea(label);
        }
        else if (type === '$f') {
            okay = this.parsef(label);
        }
        else {
            console.error('Unexpected token ' + type + ' encountered');
            return false;
        }
        return okay;
    };
    CheckMM.prototype.parsed = function () {
        var dvars = new Set();
        while (this.tokens.length) {
            var token = this.tokens[0];
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
    };
    // Parse $c statement. Return true iff okay.
    CheckMM.prototype.parsec = function () {
        if (this.scopes.length > 1) {
            console.error('$c statement occurs in inner block');
            return false;
        }
        var listempty = true;
        var _loop_4 = function () {
            var token = this_3.tokens[0];
            if (token === '$.') {
                return "break";
            }
            this_3.tokens.shift();
            listempty = false;
            if (!this_3.ismathsymboltoken(token)) {
                console.error('Attempt to declare ' + token + ' as a constant');
                return { value: false };
            }
            if (this_3.variables.has(token)) {
                console.error('Attempt to redeclare variable ' + token + ' as a constant');
                return { value: false };
            }
            if (this_3.labelused(token)) {
                console.error('Attempt to reuse label ' + token + ' as a constant');
                return { value: false };
            }
            if (this_3.constants.find(function (value) { return value === token; }) !== undefined) {
                console.error('Attempt to redeclare constant ' + token);
                return { value: false };
            }
            this_3.constants.push(token);
        };
        var this_3 = this;
        while (this.tokens.length) {
            var state_3 = _loop_4();
            if (typeof state_3 === "object")
                return state_3.value;
            if (state_3 === "break")
                break;
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
    };
    // Parse $v statement. Return true iff okay.
    CheckMM.prototype.parsev = function () {
        var listempty = true;
        var _loop_5 = function () {
            var token = this_4.tokens[0];
            if (token === '$.') {
                return "break";
            }
            this_4.tokens.shift();
            listempty = false;
            if (!this_4.ismathsymboltoken(token)) {
                console.error('Attempt to declare ' + token + ' as a variable');
                return { value: false };
            }
            if (this_4.constants.find(function (value) { return value === token; }) !== undefined) {
                console.error('Attempt to redeclare constant ' + token + ' as a variable');
                return { value: false };
            }
            if (this_4.labelused(token)) {
                console.error('Attempt to reuse label ' + token + ' as a variable');
                return { value: false };
            }
            if (this_4.isactivevariable(token)) {
                console.error('Attempt to redeclare active variable ' + token);
                return { value: false };
            }
            this_4.variables.add(token);
            this_4.scopes[this_4.scopes.length - 1].activevariables.add(token);
        };
        var this_4 = this;
        while (this.tokens.length) {
            var state_4 = _loop_5();
            if (typeof state_4 === "object")
                return state_4.value;
            if (state_4 === "break")
                break;
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
    };
    CheckMM.prototype.checkmm = function () {
        this.scopes.push(new Scope());
        while (this.tokens.length) {
            var token = this.tokens.shift();
            var okay = true;
            if (this.islabeltoken(token)) {
                okay = this.parselabel(token);
            }
            else if (token === '$d') {
                okay = this.parsed();
            }
            else if (token === '${') {
                this.scopes.push(new Scope());
            }
            else if (token === '$}') {
                this.scopes.pop();
                if (!this.scopes.length) {
                    console.error('$} without corresponding ${');
                    return false;
                }
            }
            else if (token === '$c') {
                okay = this.parsec();
            }
            else if (token === '$v') {
                okay = this.parsev();
            }
            else {
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
    };
    return CheckMM;
}(State));
exports.CheckMM = CheckMM;
var EXIT_FAILURE = 1;
function main(argv) {
    var checkmm = new CheckMM();
    if (argv.length === 3) {
        var newProofLimit = parseInt(argv[2], 10);
        if (newProofLimit) {
            checkmm.nProofLimit = newProofLimit;
        }
        else {
            console.error('Invalid proof limit' + argv[2]);
        }
        argv.pop();
    }
    if (argv.length !== 2) {
        console.error('Syntax: node checkmm.js <filename> [<proof-limit>]');
        return EXIT_FAILURE;
    }
    checkmm.setState({});
    var okay = checkmm.readtokens(argv[1]);
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
//# sourceMappingURL=checkmm.js.map