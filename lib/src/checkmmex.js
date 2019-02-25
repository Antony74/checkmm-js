"use strict";
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
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (Object.hasOwnProperty.call(mod, k)) result[k] = mod[k];
    result["default"] = mod;
    return result;
};
Object.defineProperty(exports, "__esModule", { value: true });
var checkmm_1 = require("./checkmm");
var superagent = __importStar(require("superagent"));
var CheckMMex = /** @class */ (function (_super) {
    __extends(CheckMMex, _super);
    function CheckMMex() {
        var _this = _super !== null && _super.apply(this, arguments) || this;
        _this.superagent = superagent;
        return _this;
    }
    CheckMMex.prototype.readTokensAsync = function (url, callback) {
        var _this = this;
        var alreadyencountered = this.mmFileNames.has(url);
        if (alreadyencountered) {
            callback('');
            return;
        }
        this.mmFileNames.add(url);
        this.superagent.get(url).then(function (response) {
            var _a;
            var input = response.body;
            var incomment = false;
            var infileinclusion = false;
            var newfilename = '';
            var token = '';
            while (true) {
                (_a = _this.nexttoken(input), token = _a.token, input = _a.input);
                if (!token.length) {
                    break;
                }
                if (incomment) {
                    if (token === '$)') {
                        incomment = false;
                        continue;
                    }
                    if (token.indexOf('$(') !== -1) {
                        callback('Characters $( found in a comment');
                        return;
                    }
                    if (token.indexOf('$)') !== -1) {
                        callback('Characters $) found in a comment');
                        return;
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
                            callback('Filename ' + token + ' contains a $');
                            return;
                        }
                        newfilename = token;
                        continue;
                    }
                    else {
                        if (token !== '$]') {
                            callback('Didn\'t find closing file inclusion delimiter');
                            return;
                        }
                        var okay = _this.readtokens(newfilename);
                        if (!okay) {
                            return;
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
                _this.tokens.push(token);
            }
            if (incomment) {
                callback('Unclosed comment');
                return;
            }
            if (infileinclusion) {
                callback('Unfinished file inclusion command');
                return;
            }
            callback('');
        });
    };
    return CheckMMex;
}(checkmm_1.CheckMM));
exports.CheckMMex = CheckMMex;
//# sourceMappingURL=checkmmex.js.map