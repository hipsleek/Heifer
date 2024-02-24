(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}g.z3 = f()}})(function(){var define,module,exports;return (function(){function r(e,n,t){function o(i,f){if(!n[i]){if(!e[i]){var c="function"==typeof require&&require;if(!f&&c)return c(i,!0);if(u)return u(i,!0);var a=new Error("Cannot find module '"+i+"'");throw a.code="MODULE_NOT_FOUND",a}var p=n[i]={exports:{}};e[i][0].call(p.exports,function(r){var n=e[i][1][r];return o(n||r)},p,p.exports,r,e,n,t)}return n[i].exports}for(var u="function"==typeof require&&require,i=0;i<t.length;i++)o(t[i]);return o}return r})()({1:[function(require,module,exports){
// This file is built into bundle.js via browserify

// import { init } from 'z3-solver';
const { init } = require("z3-solver");
// const process = require('process');
// import process from 'process';

var z3;

init().then((a) => {
  z3 = a;
  ocaml_ready();
  enable_buttons();
});

// function new_ctx(s) { return new Context('main'); }
// function int(ctx, n) { return ctx.Int.const(n); }
// function and(ctx, a, b) { return ctx.And(a, b); }
// function or(ctx, a, b) { return ctx.Or(a, b); }
// function implies(ctx, a, b) { return ctx.Implies(a, b); }
// function ge(ctx, a, b) { return ctx.Implies(a, b); }
// function le(ctx, a, b) { return ctx.Implies(a, b); }

function solve(f, k) {
  // console.log('solve arg', arg);
  const { Context } = z3;
  // console.log(Context);

  // const { Context } = init();
  const ctx = new Context("main");
  window.ctx = ctx;
  // const { Solver, Int, And } = ctx;
  // const x = Int.const('x');
  const solver = new ctx.Solver();
  solver.add(f(ctx));
  // solver.add(And(x.ge(0), x.le(9)));
  solver.check().then((res) => {
    k(res === "sat");
    // console.log(res);
    // console.log(typeof res);
  });
}
module.exports = { solve };
// window.solve = solve;

// console.log('hi');
// process.exit(0);
},{"z3-solver":9}],2:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
var tslib_1 = require("tslib");
var Semaphore_1 = require("./Semaphore");
var Mutex = /** @class */ (function () {
    function Mutex(cancelError) {
        this._semaphore = new Semaphore_1.default(1, cancelError);
    }
    Mutex.prototype.acquire = function () {
        return (0, tslib_1.__awaiter)(this, void 0, void 0, function () {
            var _a, releaser;
            return (0, tslib_1.__generator)(this, function (_b) {
                switch (_b.label) {
                    case 0: return [4 /*yield*/, this._semaphore.acquire()];
                    case 1:
                        _a = _b.sent(), releaser = _a[1];
                        return [2 /*return*/, releaser];
                }
            });
        });
    };
    Mutex.prototype.runExclusive = function (callback) {
        return this._semaphore.runExclusive(function () { return callback(); });
    };
    Mutex.prototype.isLocked = function () {
        return this._semaphore.isLocked();
    };
    Mutex.prototype.waitForUnlock = function () {
        return this._semaphore.waitForUnlock();
    };
    /** @deprecated Deprecated in 0.3.0, will be removed in 0.4.0. Use runExclusive instead. */
    Mutex.prototype.release = function () {
        this._semaphore.release();
    };
    Mutex.prototype.cancel = function () {
        return this._semaphore.cancel();
    };
    return Mutex;
}());
exports.default = Mutex;

},{"./Semaphore":3,"tslib":8}],3:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
var tslib_1 = require("tslib");
var errors_1 = require("./errors");
var Semaphore = /** @class */ (function () {
    function Semaphore(_maxConcurrency, _cancelError) {
        if (_cancelError === void 0) { _cancelError = errors_1.E_CANCELED; }
        this._maxConcurrency = _maxConcurrency;
        this._cancelError = _cancelError;
        this._queue = [];
        this._waiters = [];
        if (_maxConcurrency <= 0) {
            throw new Error('semaphore must be initialized to a positive value');
        }
        this._value = _maxConcurrency;
    }
    Semaphore.prototype.acquire = function () {
        var _this = this;
        var locked = this.isLocked();
        var ticketPromise = new Promise(function (resolve, reject) {
            return _this._queue.push({ resolve: resolve, reject: reject });
        });
        if (!locked)
            this._dispatch();
        return ticketPromise;
    };
    Semaphore.prototype.runExclusive = function (callback) {
        return (0, tslib_1.__awaiter)(this, void 0, void 0, function () {
            var _a, value, release;
            return (0, tslib_1.__generator)(this, function (_b) {
                switch (_b.label) {
                    case 0: return [4 /*yield*/, this.acquire()];
                    case 1:
                        _a = _b.sent(), value = _a[0], release = _a[1];
                        _b.label = 2;
                    case 2:
                        _b.trys.push([2, , 4, 5]);
                        return [4 /*yield*/, callback(value)];
                    case 3: return [2 /*return*/, _b.sent()];
                    case 4:
                        release();
                        return [7 /*endfinally*/];
                    case 5: return [2 /*return*/];
                }
            });
        });
    };
    Semaphore.prototype.waitForUnlock = function () {
        return (0, tslib_1.__awaiter)(this, void 0, void 0, function () {
            var waitPromise;
            var _this = this;
            return (0, tslib_1.__generator)(this, function (_a) {
                if (!this.isLocked()) {
                    return [2 /*return*/, Promise.resolve()];
                }
                waitPromise = new Promise(function (resolve) { return _this._waiters.push({ resolve: resolve }); });
                return [2 /*return*/, waitPromise];
            });
        });
    };
    Semaphore.prototype.isLocked = function () {
        return this._value <= 0;
    };
    /** @deprecated Deprecated in 0.3.0, will be removed in 0.4.0. Use runExclusive instead. */
    Semaphore.prototype.release = function () {
        if (this._maxConcurrency > 1) {
            throw new Error('this method is unavailable on semaphores with concurrency > 1; use the scoped release returned by acquire instead');
        }
        if (this._currentReleaser) {
            var releaser = this._currentReleaser;
            this._currentReleaser = undefined;
            releaser();
        }
    };
    Semaphore.prototype.cancel = function () {
        var _this = this;
        this._queue.forEach(function (ticket) { return ticket.reject(_this._cancelError); });
        this._queue = [];
    };
    Semaphore.prototype._dispatch = function () {
        var _this = this;
        var nextTicket = this._queue.shift();
        if (!nextTicket)
            return;
        var released = false;
        this._currentReleaser = function () {
            if (released)
                return;
            released = true;
            _this._value++;
            _this._resolveWaiters();
            _this._dispatch();
        };
        nextTicket.resolve([this._value--, this._currentReleaser]);
    };
    Semaphore.prototype._resolveWaiters = function () {
        this._waiters.forEach(function (waiter) { return waiter.resolve(); });
        this._waiters = [];
    };
    return Semaphore;
}());
exports.default = Semaphore;

},{"./errors":4,"tslib":8}],4:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.E_CANCELED = exports.E_ALREADY_LOCKED = exports.E_TIMEOUT = void 0;
exports.E_TIMEOUT = new Error('timeout while waiting for mutex to become available');
exports.E_ALREADY_LOCKED = new Error('mutex already locked');
exports.E_CANCELED = new Error('request for lock canceled');

},{}],5:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.tryAcquire = exports.withTimeout = exports.Semaphore = exports.Mutex = void 0;
var tslib_1 = require("tslib");
var Mutex_1 = require("./Mutex");
Object.defineProperty(exports, "Mutex", { enumerable: true, get: function () { return Mutex_1.default; } });
var Semaphore_1 = require("./Semaphore");
Object.defineProperty(exports, "Semaphore", { enumerable: true, get: function () { return Semaphore_1.default; } });
var withTimeout_1 = require("./withTimeout");
Object.defineProperty(exports, "withTimeout", { enumerable: true, get: function () { return withTimeout_1.withTimeout; } });
var tryAcquire_1 = require("./tryAcquire");
Object.defineProperty(exports, "tryAcquire", { enumerable: true, get: function () { return tryAcquire_1.tryAcquire; } });
(0, tslib_1.__exportStar)(require("./errors"), exports);

},{"./Mutex":2,"./Semaphore":3,"./errors":4,"./tryAcquire":6,"./withTimeout":7,"tslib":8}],6:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.tryAcquire = void 0;
var errors_1 = require("./errors");
var withTimeout_1 = require("./withTimeout");
// eslint-disable-next-lisne @typescript-eslint/explicit-module-boundary-types
function tryAcquire(sync, alreadyAcquiredError) {
    if (alreadyAcquiredError === void 0) { alreadyAcquiredError = errors_1.E_ALREADY_LOCKED; }
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    return (0, withTimeout_1.withTimeout)(sync, 0, alreadyAcquiredError);
}
exports.tryAcquire = tryAcquire;

},{"./errors":4,"./withTimeout":7}],7:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.withTimeout = void 0;
var tslib_1 = require("tslib");
var errors_1 = require("./errors");
// eslint-disable-next-line @typescript-eslint/explicit-module-boundary-types
function withTimeout(sync, timeout, timeoutError) {
    var _this = this;
    if (timeoutError === void 0) { timeoutError = errors_1.E_TIMEOUT; }
    return {
        acquire: function () {
            return new Promise(function (resolve, reject) { return (0, tslib_1.__awaiter)(_this, void 0, void 0, function () {
                var isTimeout, handle, ticket, release, e_1;
                return (0, tslib_1.__generator)(this, function (_a) {
                    switch (_a.label) {
                        case 0:
                            isTimeout = false;
                            handle = setTimeout(function () {
                                isTimeout = true;
                                reject(timeoutError);
                            }, timeout);
                            _a.label = 1;
                        case 1:
                            _a.trys.push([1, 3, , 4]);
                            return [4 /*yield*/, sync.acquire()];
                        case 2:
                            ticket = _a.sent();
                            if (isTimeout) {
                                release = Array.isArray(ticket) ? ticket[1] : ticket;
                                release();
                            }
                            else {
                                clearTimeout(handle);
                                resolve(ticket);
                            }
                            return [3 /*break*/, 4];
                        case 3:
                            e_1 = _a.sent();
                            if (!isTimeout) {
                                clearTimeout(handle);
                                reject(e_1);
                            }
                            return [3 /*break*/, 4];
                        case 4: return [2 /*return*/];
                    }
                });
            }); });
        },
        runExclusive: function (callback) {
            return (0, tslib_1.__awaiter)(this, void 0, void 0, function () {
                var release, ticket;
                return (0, tslib_1.__generator)(this, function (_a) {
                    switch (_a.label) {
                        case 0:
                            release = function () { return undefined; };
                            _a.label = 1;
                        case 1:
                            _a.trys.push([1, , 7, 8]);
                            return [4 /*yield*/, this.acquire()];
                        case 2:
                            ticket = _a.sent();
                            if (!Array.isArray(ticket)) return [3 /*break*/, 4];
                            release = ticket[1];
                            return [4 /*yield*/, callback(ticket[0])];
                        case 3: return [2 /*return*/, _a.sent()];
                        case 4:
                            release = ticket;
                            return [4 /*yield*/, callback()];
                        case 5: return [2 /*return*/, _a.sent()];
                        case 6: return [3 /*break*/, 8];
                        case 7:
                            release();
                            return [7 /*endfinally*/];
                        case 8: return [2 /*return*/];
                    }
                });
            });
        },
        /** @deprecated Deprecated in 0.3.0, will be removed in 0.4.0. Use runExclusive instead. */
        release: function () {
            sync.release();
        },
        cancel: function () {
            return sync.cancel();
        },
        waitForUnlock: function () { return sync.waitForUnlock(); },
        isLocked: function () { return sync.isLocked(); },
    };
}
exports.withTimeout = withTimeout;

},{"./errors":4,"tslib":8}],8:[function(require,module,exports){
(function (global){(function (){
/******************************************************************************
Copyright (c) Microsoft Corporation.

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.
***************************************************************************** */
/* global global, define, Symbol, Reflect, Promise, SuppressedError */
var __extends;
var __assign;
var __rest;
var __decorate;
var __param;
var __esDecorate;
var __runInitializers;
var __propKey;
var __setFunctionName;
var __metadata;
var __awaiter;
var __generator;
var __exportStar;
var __values;
var __read;
var __spread;
var __spreadArrays;
var __spreadArray;
var __await;
var __asyncGenerator;
var __asyncDelegator;
var __asyncValues;
var __makeTemplateObject;
var __importStar;
var __importDefault;
var __classPrivateFieldGet;
var __classPrivateFieldSet;
var __classPrivateFieldIn;
var __createBinding;
var __addDisposableResource;
var __disposeResources;
(function (factory) {
    var root = typeof global === "object" ? global : typeof self === "object" ? self : typeof this === "object" ? this : {};
    if (typeof define === "function" && define.amd) {
        define("tslib", ["exports"], function (exports) { factory(createExporter(root, createExporter(exports))); });
    }
    else if (typeof module === "object" && typeof module.exports === "object") {
        factory(createExporter(root, createExporter(module.exports)));
    }
    else {
        factory(createExporter(root));
    }
    function createExporter(exports, previous) {
        if (exports !== root) {
            if (typeof Object.create === "function") {
                Object.defineProperty(exports, "__esModule", { value: true });
            }
            else {
                exports.__esModule = true;
            }
        }
        return function (id, v) { return exports[id] = previous ? previous(id, v) : v; };
    }
})
(function (exporter) {
    var extendStatics = Object.setPrototypeOf ||
        ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
        function (d, b) { for (var p in b) if (Object.prototype.hasOwnProperty.call(b, p)) d[p] = b[p]; };

    __extends = function (d, b) {
        if (typeof b !== "function" && b !== null)
            throw new TypeError("Class extends value " + String(b) + " is not a constructor or null");
        extendStatics(d, b);
        function __() { this.constructor = d; }
        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
    };

    __assign = Object.assign || function (t) {
        for (var s, i = 1, n = arguments.length; i < n; i++) {
            s = arguments[i];
            for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p)) t[p] = s[p];
        }
        return t;
    };

    __rest = function (s, e) {
        var t = {};
        for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p) && e.indexOf(p) < 0)
            t[p] = s[p];
        if (s != null && typeof Object.getOwnPropertySymbols === "function")
            for (var i = 0, p = Object.getOwnPropertySymbols(s); i < p.length; i++) {
                if (e.indexOf(p[i]) < 0 && Object.prototype.propertyIsEnumerable.call(s, p[i]))
                    t[p[i]] = s[p[i]];
            }
        return t;
    };

    __decorate = function (decorators, target, key, desc) {
        var c = arguments.length, r = c < 3 ? target : desc === null ? desc = Object.getOwnPropertyDescriptor(target, key) : desc, d;
        if (typeof Reflect === "object" && typeof Reflect.decorate === "function") r = Reflect.decorate(decorators, target, key, desc);
        else for (var i = decorators.length - 1; i >= 0; i--) if (d = decorators[i]) r = (c < 3 ? d(r) : c > 3 ? d(target, key, r) : d(target, key)) || r;
        return c > 3 && r && Object.defineProperty(target, key, r), r;
    };

    __param = function (paramIndex, decorator) {
        return function (target, key) { decorator(target, key, paramIndex); }
    };

    __esDecorate = function (ctor, descriptorIn, decorators, contextIn, initializers, extraInitializers) {
        function accept(f) { if (f !== void 0 && typeof f !== "function") throw new TypeError("Function expected"); return f; }
        var kind = contextIn.kind, key = kind === "getter" ? "get" : kind === "setter" ? "set" : "value";
        var target = !descriptorIn && ctor ? contextIn["static"] ? ctor : ctor.prototype : null;
        var descriptor = descriptorIn || (target ? Object.getOwnPropertyDescriptor(target, contextIn.name) : {});
        var _, done = false;
        for (var i = decorators.length - 1; i >= 0; i--) {
            var context = {};
            for (var p in contextIn) context[p] = p === "access" ? {} : contextIn[p];
            for (var p in contextIn.access) context.access[p] = contextIn.access[p];
            context.addInitializer = function (f) { if (done) throw new TypeError("Cannot add initializers after decoration has completed"); extraInitializers.push(accept(f || null)); };
            var result = (0, decorators[i])(kind === "accessor" ? { get: descriptor.get, set: descriptor.set } : descriptor[key], context);
            if (kind === "accessor") {
                if (result === void 0) continue;
                if (result === null || typeof result !== "object") throw new TypeError("Object expected");
                if (_ = accept(result.get)) descriptor.get = _;
                if (_ = accept(result.set)) descriptor.set = _;
                if (_ = accept(result.init)) initializers.unshift(_);
            }
            else if (_ = accept(result)) {
                if (kind === "field") initializers.unshift(_);
                else descriptor[key] = _;
            }
        }
        if (target) Object.defineProperty(target, contextIn.name, descriptor);
        done = true;
    };

    __runInitializers = function (thisArg, initializers, value) {
        var useValue = arguments.length > 2;
        for (var i = 0; i < initializers.length; i++) {
            value = useValue ? initializers[i].call(thisArg, value) : initializers[i].call(thisArg);
        }
        return useValue ? value : void 0;
    };

    __propKey = function (x) {
        return typeof x === "symbol" ? x : "".concat(x);
    };

    __setFunctionName = function (f, name, prefix) {
        if (typeof name === "symbol") name = name.description ? "[".concat(name.description, "]") : "";
        return Object.defineProperty(f, "name", { configurable: true, value: prefix ? "".concat(prefix, " ", name) : name });
    };

    __metadata = function (metadataKey, metadataValue) {
        if (typeof Reflect === "object" && typeof Reflect.metadata === "function") return Reflect.metadata(metadataKey, metadataValue);
    };

    __awaiter = function (thisArg, _arguments, P, generator) {
        function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
        return new (P || (P = Promise))(function (resolve, reject) {
            function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
            function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
            function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
            step((generator = generator.apply(thisArg, _arguments || [])).next());
        });
    };

    __generator = function (thisArg, body) {
        var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g;
        return g = { next: verb(0), "throw": verb(1), "return": verb(2) }, typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;
        function verb(n) { return function (v) { return step([n, v]); }; }
        function step(op) {
            if (f) throw new TypeError("Generator is already executing.");
            while (g && (g = 0, op[0] && (_ = 0)), _) try {
                if (f = 1, y && (t = op[0] & 2 ? y["return"] : op[0] ? y["throw"] || ((t = y["return"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;
                if (y = 0, t) op = [op[0] & 2, t.value];
                switch (op[0]) {
                    case 0: case 1: t = op; break;
                    case 4: _.label++; return { value: op[1], done: false };
                    case 5: _.label++; y = op[1]; op = [0]; continue;
                    case 7: op = _.ops.pop(); _.trys.pop(); continue;
                    default:
                        if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }
                        if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }
                        if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }
                        if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }
                        if (t[2]) _.ops.pop();
                        _.trys.pop(); continue;
                }
                op = body.call(thisArg, _);
            } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }
            if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };
        }
    };

    __exportStar = function(m, o) {
        for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(o, p)) __createBinding(o, m, p);
    };

    __createBinding = Object.create ? (function(o, m, k, k2) {
        if (k2 === undefined) k2 = k;
        var desc = Object.getOwnPropertyDescriptor(m, k);
        if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
            desc = { enumerable: true, get: function() { return m[k]; } };
        }
        Object.defineProperty(o, k2, desc);
    }) : (function(o, m, k, k2) {
        if (k2 === undefined) k2 = k;
        o[k2] = m[k];
    });

    __values = function (o) {
        var s = typeof Symbol === "function" && Symbol.iterator, m = s && o[s], i = 0;
        if (m) return m.call(o);
        if (o && typeof o.length === "number") return {
            next: function () {
                if (o && i >= o.length) o = void 0;
                return { value: o && o[i++], done: !o };
            }
        };
        throw new TypeError(s ? "Object is not iterable." : "Symbol.iterator is not defined.");
    };

    __read = function (o, n) {
        var m = typeof Symbol === "function" && o[Symbol.iterator];
        if (!m) return o;
        var i = m.call(o), r, ar = [], e;
        try {
            while ((n === void 0 || n-- > 0) && !(r = i.next()).done) ar.push(r.value);
        }
        catch (error) { e = { error: error }; }
        finally {
            try {
                if (r && !r.done && (m = i["return"])) m.call(i);
            }
            finally { if (e) throw e.error; }
        }
        return ar;
    };

    /** @deprecated */
    __spread = function () {
        for (var ar = [], i = 0; i < arguments.length; i++)
            ar = ar.concat(__read(arguments[i]));
        return ar;
    };

    /** @deprecated */
    __spreadArrays = function () {
        for (var s = 0, i = 0, il = arguments.length; i < il; i++) s += arguments[i].length;
        for (var r = Array(s), k = 0, i = 0; i < il; i++)
            for (var a = arguments[i], j = 0, jl = a.length; j < jl; j++, k++)
                r[k] = a[j];
        return r;
    };

    __spreadArray = function (to, from, pack) {
        if (pack || arguments.length === 2) for (var i = 0, l = from.length, ar; i < l; i++) {
            if (ar || !(i in from)) {
                if (!ar) ar = Array.prototype.slice.call(from, 0, i);
                ar[i] = from[i];
            }
        }
        return to.concat(ar || Array.prototype.slice.call(from));
    };

    __await = function (v) {
        return this instanceof __await ? (this.v = v, this) : new __await(v);
    };

    __asyncGenerator = function (thisArg, _arguments, generator) {
        if (!Symbol.asyncIterator) throw new TypeError("Symbol.asyncIterator is not defined.");
        var g = generator.apply(thisArg, _arguments || []), i, q = [];
        return i = {}, verb("next"), verb("throw"), verb("return"), i[Symbol.asyncIterator] = function () { return this; }, i;
        function verb(n) { if (g[n]) i[n] = function (v) { return new Promise(function (a, b) { q.push([n, v, a, b]) > 1 || resume(n, v); }); }; }
        function resume(n, v) { try { step(g[n](v)); } catch (e) { settle(q[0][3], e); } }
        function step(r) { r.value instanceof __await ? Promise.resolve(r.value.v).then(fulfill, reject) : settle(q[0][2], r);  }
        function fulfill(value) { resume("next", value); }
        function reject(value) { resume("throw", value); }
        function settle(f, v) { if (f(v), q.shift(), q.length) resume(q[0][0], q[0][1]); }
    };

    __asyncDelegator = function (o) {
        var i, p;
        return i = {}, verb("next"), verb("throw", function (e) { throw e; }), verb("return"), i[Symbol.iterator] = function () { return this; }, i;
        function verb(n, f) { i[n] = o[n] ? function (v) { return (p = !p) ? { value: __await(o[n](v)), done: false } : f ? f(v) : v; } : f; }
    };

    __asyncValues = function (o) {
        if (!Symbol.asyncIterator) throw new TypeError("Symbol.asyncIterator is not defined.");
        var m = o[Symbol.asyncIterator], i;
        return m ? m.call(o) : (o = typeof __values === "function" ? __values(o) : o[Symbol.iterator](), i = {}, verb("next"), verb("throw"), verb("return"), i[Symbol.asyncIterator] = function () { return this; }, i);
        function verb(n) { i[n] = o[n] && function (v) { return new Promise(function (resolve, reject) { v = o[n](v), settle(resolve, reject, v.done, v.value); }); }; }
        function settle(resolve, reject, d, v) { Promise.resolve(v).then(function(v) { resolve({ value: v, done: d }); }, reject); }
    };

    __makeTemplateObject = function (cooked, raw) {
        if (Object.defineProperty) { Object.defineProperty(cooked, "raw", { value: raw }); } else { cooked.raw = raw; }
        return cooked;
    };

    var __setModuleDefault = Object.create ? (function(o, v) {
        Object.defineProperty(o, "default", { enumerable: true, value: v });
    }) : function(o, v) {
        o["default"] = v;
    };

    __importStar = function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
        __setModuleDefault(result, mod);
        return result;
    };

    __importDefault = function (mod) {
        return (mod && mod.__esModule) ? mod : { "default": mod };
    };

    __classPrivateFieldGet = function (receiver, state, kind, f) {
        if (kind === "a" && !f) throw new TypeError("Private accessor was defined without a getter");
        if (typeof state === "function" ? receiver !== state || !f : !state.has(receiver)) throw new TypeError("Cannot read private member from an object whose class did not declare it");
        return kind === "m" ? f : kind === "a" ? f.call(receiver) : f ? f.value : state.get(receiver);
    };

    __classPrivateFieldSet = function (receiver, state, value, kind, f) {
        if (kind === "m") throw new TypeError("Private method is not writable");
        if (kind === "a" && !f) throw new TypeError("Private accessor was defined without a setter");
        if (typeof state === "function" ? receiver !== state || !f : !state.has(receiver)) throw new TypeError("Cannot write private member to an object whose class did not declare it");
        return (kind === "a" ? f.call(receiver, value) : f ? f.value = value : state.set(receiver, value)), value;
    };

    __classPrivateFieldIn = function (state, receiver) {
        if (receiver === null || (typeof receiver !== "object" && typeof receiver !== "function")) throw new TypeError("Cannot use 'in' operator on non-object");
        return typeof state === "function" ? receiver === state : state.has(receiver);
    };

    __addDisposableResource = function (env, value, async) {
        if (value !== null && value !== void 0) {
            if (typeof value !== "object" && typeof value !== "function") throw new TypeError("Object expected.");
            var dispose;
            if (async) {
                if (!Symbol.asyncDispose) throw new TypeError("Symbol.asyncDispose is not defined.");
                dispose = value[Symbol.asyncDispose];
            }
            if (dispose === void 0) {
                if (!Symbol.dispose) throw new TypeError("Symbol.dispose is not defined.");
                dispose = value[Symbol.dispose];
            }
            if (typeof dispose !== "function") throw new TypeError("Object not disposable.");
            env.stack.push({ value: value, dispose: dispose, async: async });
        }
        else if (async) {
            env.stack.push({ async: true });
        }
        return value;
    };

    var _SuppressedError = typeof SuppressedError === "function" ? SuppressedError : function (error, suppressed, message) {
        var e = new Error(message);
        return e.name = "SuppressedError", e.error = error, e.suppressed = suppressed, e;
    };

    __disposeResources = function (env) {
        function fail(e) {
            env.error = env.hasError ? new _SuppressedError(e, env.error, "An error was suppressed during disposal.") : e;
            env.hasError = true;
        }
        function next() {
            while (env.stack.length) {
                var rec = env.stack.pop();
                try {
                    var result = rec.dispose && rec.dispose.call(rec.value);
                    if (rec.async) return Promise.resolve(result).then(next, function(e) { fail(e); return next(); });
                }
                catch (e) {
                    fail(e);
                }
            }
            if (env.hasError) throw env.error;
        }
        return next();
    };

    exporter("__extends", __extends);
    exporter("__assign", __assign);
    exporter("__rest", __rest);
    exporter("__decorate", __decorate);
    exporter("__param", __param);
    exporter("__esDecorate", __esDecorate);
    exporter("__runInitializers", __runInitializers);
    exporter("__propKey", __propKey);
    exporter("__setFunctionName", __setFunctionName);
    exporter("__metadata", __metadata);
    exporter("__awaiter", __awaiter);
    exporter("__generator", __generator);
    exporter("__exportStar", __exportStar);
    exporter("__createBinding", __createBinding);
    exporter("__values", __values);
    exporter("__read", __read);
    exporter("__spread", __spread);
    exporter("__spreadArrays", __spreadArrays);
    exporter("__spreadArray", __spreadArray);
    exporter("__await", __await);
    exporter("__asyncGenerator", __asyncGenerator);
    exporter("__asyncDelegator", __asyncDelegator);
    exporter("__asyncValues", __asyncValues);
    exporter("__makeTemplateObject", __makeTemplateObject);
    exporter("__importStar", __importStar);
    exporter("__importDefault", __importDefault);
    exporter("__classPrivateFieldGet", __classPrivateFieldGet);
    exporter("__classPrivateFieldSet", __classPrivateFieldSet);
    exporter("__classPrivateFieldIn", __classPrivateFieldIn);
    exporter("__addDisposableResource", __addDisposableResource);
    exporter("__disposeResources", __disposeResources);
});

}).call(this)}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})
},{}],9:[function(require,module,exports){
(function (global){(function (){
"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __exportStar = (this && this.__exportStar) || function(m, exports) {
    for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.init = void 0;
const high_level_1 = require("./high-level");
const low_level_1 = require("./low-level");
__exportStar(require("./high-level/types"), exports);
__exportStar(require("./low-level/types.__GENERATED__"), exports);
async function init() {
    const initZ3 = global.initZ3;
    if (initZ3 === undefined) {
        throw new Error('initZ3 was not imported correctly. Please consult documentation on how to load Z3 in browser');
    }
    const lowLevel = await (0, low_level_1.init)(initZ3);
    const highLevel = (0, high_level_1.createApi)(lowLevel.Z3);
    return { ...lowLevel, ...highLevel };
}
exports.init = init;

}).call(this)}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})
},{"./high-level":11,"./high-level/types":12,"./low-level":14,"./low-level/types.__GENERATED__":15}],10:[function(require,module,exports){
(function (global){(function (){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.createApi = void 0;
// TODO(ritave): Add typing for Context Options
//               https://github.com/Z3Prover/z3/pull/6048#discussion_r883391669
// TODO(ritave): Add an error handler
// TODO(ritave): Add support for building faster floats without support for Safari
// TODO(ritave): Use Z3_DECLARE_CLOSURE macro to generate code https://github.com/Z3Prover/z3/pull/6048#discussion_r884155462
// TODO(ritave): Add pretty printing
// TODO(ritave): Make Z3 multi-threaded
// TODO(ritave): If a test times out, jest kills it, and the global state of Z3 is left in an unexpected state.
//               This occurs specifically during longer check(). Afterwards, all next tests will fail to run
//               thinking the previous call was not finished. Find a way to stop execution and clean up the global state
const async_mutex_1 = require("async-mutex");
const low_level_1 = require("../low-level");
const types_1 = require("./types");
const utils_1 = require("./utils");
const FALLBACK_PRECISION = 17;
const asyncMutex = new async_mutex_1.Mutex();
function isCoercibleRational(obj) {
    // prettier-ignore
    const r = ((obj !== null &&
        (typeof obj === 'object' || typeof obj === 'function')) &&
        (obj.numerator !== null &&
            (typeof obj.numerator === 'number' || typeof obj.numerator === 'bigint')) &&
        (obj.denominator !== null &&
            (typeof obj.denominator === 'number' || typeof obj.denominator === 'bigint')));
    r &&
        (0, utils_1.assert)((typeof obj.numerator !== 'number' || Number.isSafeInteger(obj.numerator)) &&
            (typeof obj.denominator !== 'number' || Number.isSafeInteger(obj.denominator)), 'Fraction numerator and denominator must be integers');
    return r;
}
function createApi(Z3) {
    // TODO(ritave): Create a custom linting rule that checks if the provided callbacks to cleanup
    //               Don't capture `this`
    const cleanup = new FinalizationRegistry(callback => callback());
    function enableTrace(tag) {
        Z3.enable_trace(tag);
    }
    function disableTrace(tag) {
        Z3.disable_trace(tag);
    }
    function getVersion() {
        return Z3.get_version();
    }
    function getVersionString() {
        const { major, minor, build_number } = Z3.get_version();
        return `${major}.${minor}.${build_number}`;
    }
    function getFullVersion() {
        return Z3.get_full_version();
    }
    function openLog(filename) {
        return Z3.open_log(filename);
    }
    function appendLog(s) {
        Z3.append_log(s);
    }
    function setParam(key, value) {
        if (typeof key === 'string') {
            Z3.global_param_set(key, value.toString());
        }
        else {
            (0, utils_1.assert)(value === undefined, "Can't provide a Record and second parameter to set_param at the same time");
            Object.entries(key).forEach(([key, value]) => setParam(key, value));
        }
    }
    function resetParams() {
        Z3.global_param_reset_all();
    }
    function getParam(name) {
        return Z3.global_param_get(name);
    }
    function createContext(name, options) {
        const cfg = Z3.mk_config();
        if (options != null) {
            Object.entries(options).forEach(([key, value]) => check(Z3.set_param_value(cfg, key, value.toString())));
        }
        const contextPtr = Z3.mk_context_rc(cfg);
        Z3.set_ast_print_mode(contextPtr, low_level_1.Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);
        Z3.del_config(cfg);
        function _assertContext(...ctxs) {
            ctxs.forEach(other => (0, utils_1.assert)('ctx' in other ? ctx === other.ctx : ctx === other, 'Context mismatch'));
        }
        // call this after every nontrivial call to the underlying API
        function throwIfError() {
            if (Z3.get_error_code(contextPtr) !== low_level_1.Z3_error_code.Z3_OK) {
                throw new Error(Z3.get_error_msg(ctx.ptr, Z3.get_error_code(ctx.ptr)));
            }
        }
        function check(val) {
            throwIfError();
            return val;
        }
        /////////////
        // Private //
        /////////////
        function _toSymbol(s) {
            if (typeof s === 'number') {
                return check(Z3.mk_int_symbol(contextPtr, s));
            }
            else {
                return check(Z3.mk_string_symbol(contextPtr, s));
            }
        }
        function _fromSymbol(sym) {
            const kind = check(Z3.get_symbol_kind(contextPtr, sym));
            switch (kind) {
                case low_level_1.Z3_symbol_kind.Z3_INT_SYMBOL:
                    return Z3.get_symbol_int(contextPtr, sym);
                case low_level_1.Z3_symbol_kind.Z3_STRING_SYMBOL:
                    return Z3.get_symbol_string(contextPtr, sym);
                default:
                    (0, utils_1.assertExhaustive)(kind);
            }
        }
        function _toParams(key, value) {
            const params = Z3.mk_params(contextPtr);
            Z3.params_inc_ref(contextPtr, params);
            // If value is a boolean
            if (typeof value === 'boolean') {
                Z3.params_set_bool(contextPtr, params, _toSymbol(key), value);
            }
            else if (typeof value === 'number') {
                // If value is a uint
                if (Number.isInteger(value)) {
                    check(Z3.params_set_uint(contextPtr, params, _toSymbol(key), value));
                }
                else {
                    // If value is a double
                    check(Z3.params_set_double(contextPtr, params, _toSymbol(key), value));
                }
            }
            else if (typeof value === 'string') {
                check(Z3.params_set_symbol(contextPtr, params, _toSymbol(key), _toSymbol(value)));
            }
            return params;
        }
        function _toAst(ast) {
            switch (check(Z3.get_ast_kind(contextPtr, ast))) {
                case low_level_1.Z3_ast_kind.Z3_SORT_AST:
                    return _toSort(ast);
                case low_level_1.Z3_ast_kind.Z3_FUNC_DECL_AST:
                    return new FuncDeclImpl(ast);
                default:
                    return _toExpr(ast);
            }
        }
        function _toSort(ast) {
            switch (check(Z3.get_sort_kind(contextPtr, ast))) {
                case low_level_1.Z3_sort_kind.Z3_BOOL_SORT:
                    return new BoolSortImpl(ast);
                case low_level_1.Z3_sort_kind.Z3_INT_SORT:
                case low_level_1.Z3_sort_kind.Z3_REAL_SORT:
                    return new ArithSortImpl(ast);
                case low_level_1.Z3_sort_kind.Z3_BV_SORT:
                    return new BitVecSortImpl(ast);
                case low_level_1.Z3_sort_kind.Z3_ARRAY_SORT:
                    return new ArraySortImpl(ast);
                default:
                    return new SortImpl(ast);
            }
        }
        function _toExpr(ast) {
            const kind = check(Z3.get_ast_kind(contextPtr, ast));
            if (kind === low_level_1.Z3_ast_kind.Z3_QUANTIFIER_AST) {
                if (Z3.is_lambda(contextPtr, ast)) {
                    return new LambdaImpl(ast);
                }
                return new NonLambdaQuantifierImpl(ast);
            }
            const sortKind = check(Z3.get_sort_kind(contextPtr, Z3.get_sort(contextPtr, ast)));
            switch (sortKind) {
                case low_level_1.Z3_sort_kind.Z3_BOOL_SORT:
                    return new BoolImpl(ast);
                case low_level_1.Z3_sort_kind.Z3_INT_SORT:
                    if (kind === low_level_1.Z3_ast_kind.Z3_NUMERAL_AST) {
                        return new IntNumImpl(ast);
                    }
                    return new ArithImpl(ast);
                case low_level_1.Z3_sort_kind.Z3_REAL_SORT:
                    if (kind === low_level_1.Z3_ast_kind.Z3_NUMERAL_AST) {
                        return new RatNumImpl(ast);
                    }
                    return new ArithImpl(ast);
                case low_level_1.Z3_sort_kind.Z3_BV_SORT:
                    if (kind === low_level_1.Z3_ast_kind.Z3_NUMERAL_AST) {
                        return new BitVecNumImpl(ast);
                    }
                    return new BitVecImpl(ast);
                case low_level_1.Z3_sort_kind.Z3_ARRAY_SORT:
                    return new ArrayImpl(ast);
                default:
                    return new ExprImpl(ast);
            }
        }
        function _flattenArgs(args) {
            const result = [];
            for (const arg of args) {
                if (isAstVector(arg)) {
                    result.push(...arg.values());
                }
                else {
                    result.push(arg);
                }
            }
            return result;
        }
        function _toProbe(p) {
            if (isProbe(p)) {
                return p;
            }
            return new ProbeImpl(p);
        }
        function _probeNary(f, args) {
            (0, utils_1.assert)(args.length > 0, 'At least one argument expected');
            let r = _toProbe(args[0]);
            for (let i = 1; i < args.length; i++) {
                r = new ProbeImpl(check(f(contextPtr, r.ptr, _toProbe(args[i]).ptr)));
            }
            return r;
        }
        ///////////////
        // Functions //
        ///////////////
        function interrupt() {
            check(Z3.interrupt(contextPtr));
        }
        function isModel(obj) {
            const r = obj instanceof ModelImpl;
            r && _assertContext(obj);
            return r;
        }
        function isAst(obj) {
            const r = obj instanceof AstImpl;
            r && _assertContext(obj);
            return r;
        }
        function isSort(obj) {
            const r = obj instanceof SortImpl;
            r && _assertContext(obj);
            return r;
        }
        function isFuncDecl(obj) {
            const r = obj instanceof FuncDeclImpl;
            r && _assertContext(obj);
            return r;
        }
        function isFuncInterp(obj) {
            const r = obj instanceof FuncInterpImpl;
            r && _assertContext(obj);
            return r;
        }
        function isApp(obj) {
            if (!isExpr(obj)) {
                return false;
            }
            const kind = check(Z3.get_ast_kind(contextPtr, obj.ast));
            return kind === low_level_1.Z3_ast_kind.Z3_NUMERAL_AST || kind === low_level_1.Z3_ast_kind.Z3_APP_AST;
        }
        function isConst(obj) {
            return isExpr(obj) && isApp(obj) && obj.numArgs() === 0;
        }
        function isExpr(obj) {
            const r = obj instanceof ExprImpl;
            r && _assertContext(obj);
            return r;
        }
        function isVar(obj) {
            return isExpr(obj) && check(Z3.get_ast_kind(contextPtr, obj.ast)) === low_level_1.Z3_ast_kind.Z3_VAR_AST;
        }
        function isAppOf(obj, kind) {
            return isExpr(obj) && isApp(obj) && obj.decl().kind() === kind;
        }
        function isBool(obj) {
            const r = obj instanceof ExprImpl && obj.sort.kind() === low_level_1.Z3_sort_kind.Z3_BOOL_SORT;
            r && _assertContext(obj);
            return r;
        }
        function isTrue(obj) {
            return isAppOf(obj, low_level_1.Z3_decl_kind.Z3_OP_TRUE);
        }
        function isFalse(obj) {
            return isAppOf(obj, low_level_1.Z3_decl_kind.Z3_OP_FALSE);
        }
        function isAnd(obj) {
            return isAppOf(obj, low_level_1.Z3_decl_kind.Z3_OP_AND);
        }
        function isOr(obj) {
            return isAppOf(obj, low_level_1.Z3_decl_kind.Z3_OP_OR);
        }
        function isImplies(obj) {
            return isAppOf(obj, low_level_1.Z3_decl_kind.Z3_OP_IMPLIES);
        }
        function isNot(obj) {
            return isAppOf(obj, low_level_1.Z3_decl_kind.Z3_OP_NOT);
        }
        function isEq(obj) {
            return isAppOf(obj, low_level_1.Z3_decl_kind.Z3_OP_EQ);
        }
        function isDistinct(obj) {
            return isAppOf(obj, low_level_1.Z3_decl_kind.Z3_OP_DISTINCT);
        }
        function isQuantifier(obj) {
            const r = obj instanceof QuantifierImpl;
            r && _assertContext(obj);
            return r;
        }
        function isArith(obj) {
            const r = obj instanceof ArithImpl;
            r && _assertContext(obj);
            return r;
        }
        function isArithSort(obj) {
            const r = obj instanceof ArithSortImpl;
            r && _assertContext(obj);
            return r;
        }
        function isInt(obj) {
            return isArith(obj) && isIntSort(obj.sort);
        }
        function isIntVal(obj) {
            const r = obj instanceof IntNumImpl;
            r && _assertContext(obj);
            return r;
        }
        function isIntSort(obj) {
            return isSort(obj) && obj.kind() === low_level_1.Z3_sort_kind.Z3_INT_SORT;
        }
        function isReal(obj) {
            return isArith(obj) && isRealSort(obj.sort);
        }
        function isRealVal(obj) {
            const r = obj instanceof RatNumImpl;
            r && _assertContext(obj);
            return r;
        }
        function isRealSort(obj) {
            return isSort(obj) && obj.kind() === low_level_1.Z3_sort_kind.Z3_REAL_SORT;
        }
        function isBitVecSort(obj) {
            const r = obj instanceof BitVecSortImpl;
            r && _assertContext(obj);
            return r;
        }
        function isBitVec(obj) {
            const r = obj instanceof BitVecImpl;
            r && _assertContext(obj);
            return r;
        }
        function isBitVecVal(obj) {
            const r = obj instanceof BitVecNumImpl;
            r && _assertContext(obj);
            return r;
        }
        function isArraySort(obj) {
            const r = obj instanceof ArraySortImpl;
            r && _assertContext(obj);
            return r;
        }
        function isArray(obj) {
            const r = obj instanceof ArrayImpl;
            r && _assertContext(obj);
            return r;
        }
        function isConstArray(obj) {
            return isAppOf(obj, low_level_1.Z3_decl_kind.Z3_OP_CONST_ARRAY);
        }
        function isProbe(obj) {
            const r = obj instanceof ProbeImpl;
            r && _assertContext(obj);
            return r;
        }
        function isTactic(obj) {
            const r = obj instanceof TacticImpl;
            r && _assertContext(obj);
            return r;
        }
        function isAstVector(obj) {
            const r = obj instanceof AstVectorImpl;
            r && _assertContext(obj);
            return r;
        }
        function eqIdentity(a, b) {
            return a.eqIdentity(b);
        }
        function getVarIndex(obj) {
            (0, utils_1.assert)(isVar(obj), 'Z3 bound variable expected');
            return Z3.get_index_value(contextPtr, obj.ast);
        }
        function from(value) {
            if (typeof value === 'boolean') {
                return Bool.val(value);
            }
            else if (typeof value === 'number') {
                if (!Number.isFinite(value)) {
                    throw new Error(`cannot represent infinity/NaN (got ${value})`);
                }
                if (Math.floor(value) === value) {
                    return Int.val(value);
                }
                return Real.val(value);
            }
            else if (isCoercibleRational(value)) {
                return Real.val(value);
            }
            else if (typeof value === 'bigint') {
                return Int.val(value);
            }
            else if (isExpr(value)) {
                return value;
            }
            (0, utils_1.assert)(false);
        }
        async function solve(...assertions) {
            const solver = new ctx.Solver();
            solver.add(...assertions);
            const result = await solver.check();
            if (result === 'sat') {
                return solver.model();
            }
            return result;
        }
        ///////////////////////////////
        // expression simplification //
        ///////////////////////////////
        async function simplify(e) {
            const result = await Z3.simplify(contextPtr, e.ast);
            return _toExpr(check(result));
        }
        /////////////
        // Objects //
        /////////////
        const Sort = {
            declare: (name) => new SortImpl(Z3.mk_uninterpreted_sort(contextPtr, _toSymbol(name))),
        };
        const Function = {
            declare: (name, ...signature) => {
                const arity = signature.length - 1;
                const rng = signature[arity];
                _assertContext(rng);
                const dom = [];
                for (let i = 0; i < arity; i++) {
                    _assertContext(signature[i]);
                    dom.push(signature[i].ptr);
                }
                return new FuncDeclImpl(Z3.mk_func_decl(contextPtr, _toSymbol(name), dom, rng.ptr));
            },
            fresh: (...signature) => {
                const arity = signature.length - 1;
                const rng = signature[arity];
                _assertContext(rng);
                const dom = [];
                for (let i = 0; i < arity; i++) {
                    _assertContext(signature[i]);
                    dom.push(signature[i].ptr);
                }
                return new FuncDeclImpl(Z3.mk_fresh_func_decl(contextPtr, 'f', dom, rng.ptr));
            },
        };
        const RecFunc = {
            declare: (name, ...signature) => {
                const arity = signature.length - 1;
                const rng = signature[arity];
                _assertContext(rng);
                const dom = [];
                for (let i = 0; i < arity; i++) {
                    _assertContext(signature[i]);
                    dom.push(signature[i].ptr);
                }
                return new FuncDeclImpl(Z3.mk_rec_func_decl(contextPtr, _toSymbol(name), dom, rng.ptr));
            },
            addDefinition: (f, args, body) => {
                _assertContext(f, ...args, body);
                check(Z3.add_rec_def(contextPtr, f.ptr, args.map(arg => arg.ast), body.ast));
            },
        };
        const Bool = {
            sort: () => new BoolSortImpl(Z3.mk_bool_sort(contextPtr)),
            const: (name) => new BoolImpl(Z3.mk_const(contextPtr, _toSymbol(name), Bool.sort().ptr)),
            consts: (names) => {
                if (typeof names === 'string') {
                    names = names.split(' ');
                }
                return names.map(name => Bool.const(name));
            },
            vector: (prefix, count) => {
                const result = [];
                for (let i = 0; i < count; i++) {
                    result.push(Bool.const(`${prefix}__${i}`));
                }
                return result;
            },
            fresh: (prefix = 'b') => new BoolImpl(Z3.mk_fresh_const(contextPtr, prefix, Bool.sort().ptr)),
            val: (value) => {
                if (value) {
                    return new BoolImpl(Z3.mk_true(contextPtr));
                }
                return new BoolImpl(Z3.mk_false(contextPtr));
            },
        };
        const Int = {
            sort: () => new ArithSortImpl(Z3.mk_int_sort(contextPtr)),
            const: (name) => new ArithImpl(Z3.mk_const(contextPtr, _toSymbol(name), Int.sort().ptr)),
            consts: (names) => {
                if (typeof names === 'string') {
                    names = names.split(' ');
                }
                return names.map(name => Int.const(name));
            },
            vector: (prefix, count) => {
                const result = [];
                for (let i = 0; i < count; i++) {
                    result.push(Int.const(`${prefix}__${i}`));
                }
                return result;
            },
            fresh: (prefix = 'x') => new ArithImpl(Z3.mk_fresh_const(contextPtr, prefix, Int.sort().ptr)),
            val: (value) => {
                (0, utils_1.assert)(typeof value === 'bigint' || typeof value === 'string' || Number.isSafeInteger(value));
                return new IntNumImpl(check(Z3.mk_numeral(contextPtr, value.toString(), Int.sort().ptr)));
            },
        };
        const Real = {
            sort: () => new ArithSortImpl(Z3.mk_real_sort(contextPtr)),
            const: (name) => new ArithImpl(check(Z3.mk_const(contextPtr, _toSymbol(name), Real.sort().ptr))),
            consts: (names) => {
                if (typeof names === 'string') {
                    names = names.split(' ');
                }
                return names.map(name => Real.const(name));
            },
            vector: (prefix, count) => {
                const result = [];
                for (let i = 0; i < count; i++) {
                    result.push(Real.const(`${prefix}__${i}`));
                }
                return result;
            },
            fresh: (prefix = 'b') => new ArithImpl(Z3.mk_fresh_const(contextPtr, prefix, Real.sort().ptr)),
            val: (value) => {
                if (isCoercibleRational(value)) {
                    value = `${value.numerator}/${value.denominator}`;
                }
                return new RatNumImpl(Z3.mk_numeral(contextPtr, value.toString(), Real.sort().ptr));
            },
        };
        const BitVec = {
            sort(bits) {
                (0, utils_1.assert)(Number.isSafeInteger(bits), 'number of bits must be an integer');
                return new BitVecSortImpl(Z3.mk_bv_sort(contextPtr, bits));
            },
            const(name, bits) {
                return new BitVecImpl(check(Z3.mk_const(contextPtr, _toSymbol(name), isBitVecSort(bits) ? bits.ptr : BitVec.sort(bits).ptr)));
            },
            consts(names, bits) {
                if (typeof names === 'string') {
                    names = names.split(' ');
                }
                return names.map(name => BitVec.const(name, bits));
            },
            val(value, bits) {
                if (value === true) {
                    return BitVec.val(1, bits);
                }
                else if (value === false) {
                    return BitVec.val(0, bits);
                }
                return new BitVecNumImpl(check(Z3.mk_numeral(contextPtr, value.toString(), isBitVecSort(bits) ? bits.ptr : BitVec.sort(bits).ptr)));
            },
        };
        const Array = {
            sort(...sig) {
                const arity = sig.length - 1;
                const r = sig[arity];
                const d = sig[0];
                if (arity === 1) {
                    return new ArraySortImpl(Z3.mk_array_sort(contextPtr, d.ptr, r.ptr));
                }
                const dom = sig.slice(0, arity);
                return new ArraySortImpl(Z3.mk_array_sort_n(contextPtr, dom.map(s => s.ptr), r.ptr));
            },
            const(name, ...sig) {
                return new ArrayImpl(check(Z3.mk_const(contextPtr, _toSymbol(name), Array.sort(...sig).ptr)));
            },
            consts(names, ...sig) {
                if (typeof names === 'string') {
                    names = names.split(' ');
                }
                return names.map(name => Array.const(name, ...sig));
            },
            K(domain, value) {
                return new ArrayImpl(check(Z3.mk_const_array(contextPtr, domain.ptr, value.ptr)));
            },
        };
        function If(condition, onTrue, onFalse) {
            if (isProbe(condition) && isTactic(onTrue) && isTactic(onFalse)) {
                return Cond(condition, onTrue, onFalse);
            }
            (0, utils_1.assert)(!isProbe(condition) && !isTactic(onTrue) && !isTactic(onFalse), 'Mixed expressions and goals');
            if (typeof condition === 'boolean') {
                condition = Bool.val(condition);
            }
            onTrue = from(onTrue);
            onFalse = from(onFalse);
            return _toExpr(check(Z3.mk_ite(contextPtr, condition.ptr, onTrue.ast, onFalse.ast)));
        }
        function Distinct(...exprs) {
            (0, utils_1.assert)(exprs.length > 0, "Can't make Distinct ouf of nothing");
            return new BoolImpl(check(Z3.mk_distinct(contextPtr, exprs.map(expr => {
                expr = from(expr);
                _assertContext(expr);
                return expr.ast;
            }))));
        }
        function Const(name, sort) {
            _assertContext(sort);
            return _toExpr(check(Z3.mk_const(contextPtr, _toSymbol(name), sort.ptr)));
        }
        function Consts(names, sort) {
            _assertContext(sort);
            if (typeof names === 'string') {
                names = names.split(' ');
            }
            return names.map(name => Const(name, sort));
        }
        function FreshConst(sort, prefix = 'c') {
            _assertContext(sort);
            return _toExpr(Z3.mk_fresh_const(sort.ctx.ptr, prefix, sort.ptr));
        }
        function Var(idx, sort) {
            _assertContext(sort);
            return _toExpr(Z3.mk_bound(sort.ctx.ptr, idx, sort.ptr));
        }
        function Implies(a, b) {
            a = from(a);
            b = from(b);
            _assertContext(a, b);
            return new BoolImpl(check(Z3.mk_implies(contextPtr, a.ptr, b.ptr)));
        }
        function Iff(a, b) {
            a = from(a);
            b = from(b);
            _assertContext(a, b);
            return new BoolImpl(check(Z3.mk_iff(contextPtr, a.ptr, b.ptr)));
        }
        function Eq(a, b) {
            a = from(a);
            b = from(b);
            _assertContext(a, b);
            return a.eq(b);
        }
        function Xor(a, b) {
            a = from(a);
            b = from(b);
            _assertContext(a, b);
            return new BoolImpl(check(Z3.mk_xor(contextPtr, a.ptr, b.ptr)));
        }
        function Not(a) {
            if (typeof a === 'boolean') {
                a = from(a);
            }
            _assertContext(a);
            if (isProbe(a)) {
                return new ProbeImpl(check(Z3.probe_not(contextPtr, a.ptr)));
            }
            return new BoolImpl(check(Z3.mk_not(contextPtr, a.ptr)));
        }
        function And(...args) {
            if (args.length == 1 && args[0] instanceof ctx.AstVector) {
                args = [...args[0].values()];
                (0, utils_1.assert)((0, utils_1.allSatisfy)(args, isBool) ?? true, 'AstVector containing not bools');
            }
            const allProbes = (0, utils_1.allSatisfy)(args, isProbe) ?? false;
            if (allProbes) {
                return _probeNary(Z3.probe_and, args);
            }
            else {
                const castArgs = args.map(from);
                _assertContext(...castArgs);
                return new BoolImpl(check(Z3.mk_and(contextPtr, castArgs.map(arg => arg.ptr))));
            }
        }
        function Or(...args) {
            if (args.length == 1 && args[0] instanceof ctx.AstVector) {
                args = [...args[0].values()];
                (0, utils_1.assert)((0, utils_1.allSatisfy)(args, isBool) ?? true, 'AstVector containing not bools');
            }
            const allProbes = (0, utils_1.allSatisfy)(args, isProbe) ?? false;
            if (allProbes) {
                return _probeNary(Z3.probe_or, args);
            }
            else {
                const castArgs = args.map(from);
                _assertContext(...castArgs);
                return new BoolImpl(check(Z3.mk_or(contextPtr, castArgs.map(arg => arg.ptr))));
            }
        }
        function ForAll(quantifiers, body, weight = 1) {
            // Verify all quantifiers are constants
            if (!(0, utils_1.allSatisfy)(quantifiers, isConst)) {
                throw new Error('Quantifier variables must be constants');
            }
            return new NonLambdaQuantifierImpl(check(Z3.mk_quantifier_const_ex(contextPtr, true, weight, _toSymbol(''), _toSymbol(''), quantifiers.map(q => q.ptr), // The earlier check verifies these are all apps
            [], [], body.ptr)));
        }
        function Exists(quantifiers, body, weight = 1) {
            // Verify all quantifiers are constants
            if (!(0, utils_1.allSatisfy)(quantifiers, isConst)) {
                throw new Error('Quantifier variables must be constants');
            }
            return new NonLambdaQuantifierImpl(check(Z3.mk_quantifier_const_ex(contextPtr, false, weight, _toSymbol(''), _toSymbol(''), quantifiers.map(q => q.ptr), // The earlier check verifies these are all apps
            [], [], body.ptr)));
        }
        function Lambda(quantifiers, expr) {
            // TODO(walden): For some reason LambdaImpl<DomainSort, RangeSort> leads to type issues
            //    and Typescript won't build. I'm not sure why since the types seem to all match
            //    up. For now, we just use any for the domain sort
            // Verify all quantifiers are constants
            if (!(0, utils_1.allSatisfy)(quantifiers, isConst)) {
                throw new Error('Quantifier variables must be constants');
            }
            return new LambdaImpl(check(Z3.mk_lambda_const(contextPtr, quantifiers.map(q => q.ptr), expr.ptr)));
        }
        function ToReal(expr) {
            expr = from(expr);
            _assertContext(expr);
            (0, utils_1.assert)(isInt(expr), 'Int expression expected');
            return new ArithImpl(check(Z3.mk_int2real(contextPtr, expr.ast)));
        }
        function ToInt(expr) {
            if (!isExpr(expr)) {
                expr = Real.val(expr);
            }
            _assertContext(expr);
            (0, utils_1.assert)(isReal(expr), 'Real expression expected');
            return new ArithImpl(check(Z3.mk_real2int(contextPtr, expr.ast)));
        }
        function IsInt(expr) {
            if (!isExpr(expr)) {
                expr = Real.val(expr);
            }
            _assertContext(expr);
            (0, utils_1.assert)(isReal(expr), 'Real expression expected');
            return new BoolImpl(check(Z3.mk_is_int(contextPtr, expr.ast)));
        }
        function Sqrt(a) {
            if (!isExpr(a)) {
                a = Real.val(a);
            }
            return a.pow('1/2');
        }
        function Cbrt(a) {
            if (!isExpr(a)) {
                a = Real.val(a);
            }
            return a.pow('1/3');
        }
        function BV2Int(a, isSigned) {
            _assertContext(a);
            return new ArithImpl(check(Z3.mk_bv2int(contextPtr, a.ast, isSigned)));
        }
        function Int2BV(a, bits) {
            if (isArith(a)) {
                (0, utils_1.assert)(isInt(a), 'parameter must be an integer');
            }
            else {
                (0, utils_1.assert)(typeof a !== 'number' || Number.isSafeInteger(a), 'parameter must not have decimal places');
                a = Int.val(a);
            }
            return new BitVecImpl(check(Z3.mk_int2bv(contextPtr, bits, a.ast)));
        }
        function Concat(...bitvecs) {
            _assertContext(...bitvecs);
            return bitvecs.reduce((prev, curr) => new BitVecImpl(check(Z3.mk_concat(contextPtr, prev.ast, curr.ast))));
        }
        function Cond(probe, onTrue, onFalse) {
            _assertContext(probe, onTrue, onFalse);
            return new TacticImpl(check(Z3.tactic_cond(contextPtr, probe.ptr, onTrue.ptr, onFalse.ptr)));
        }
        function LT(a, b) {
            return new BoolImpl(check(Z3.mk_lt(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function GT(a, b) {
            return new BoolImpl(check(Z3.mk_gt(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function LE(a, b) {
            return new BoolImpl(check(Z3.mk_le(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function GE(a, b) {
            return new BoolImpl(check(Z3.mk_ge(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function ULT(a, b) {
            return new BoolImpl(check(Z3.mk_bvult(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function UGT(a, b) {
            return new BoolImpl(check(Z3.mk_bvugt(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function ULE(a, b) {
            return new BoolImpl(check(Z3.mk_bvule(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function UGE(a, b) {
            return new BoolImpl(check(Z3.mk_bvuge(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function SLT(a, b) {
            return new BoolImpl(check(Z3.mk_bvslt(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function SGT(a, b) {
            return new BoolImpl(check(Z3.mk_bvsgt(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function SLE(a, b) {
            return new BoolImpl(check(Z3.mk_bvsle(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function SGE(a, b) {
            return new BoolImpl(check(Z3.mk_bvsge(contextPtr, a.ast, a.sort.cast(b).ast)));
        }
        function Extract(hi, lo, val) {
            return new BitVecImpl(check(Z3.mk_extract(contextPtr, hi, lo, val.ast)));
        }
        function Select(array, ...indices) {
            const args = indices.map((arg, i) => array.domain_n(i).cast(arg));
            if (args.length === 1) {
                return _toExpr(check(Z3.mk_select(contextPtr, array.ast, args[0].ast)));
            }
            const _args = args.map(arg => arg.ast);
            return _toExpr(check(Z3.mk_select_n(contextPtr, array.ast, _args)));
        }
        function Store(array, ...indicesAndValue) {
            const args = indicesAndValue.map((arg, i) => {
                if (i === indicesAndValue.length - 1) {
                    return array.range().cast(arg);
                }
                return array.domain_n(i).cast(arg);
            });
            if (args.length <= 1) {
                throw new Error('Array store requires both index and value arguments');
            }
            if (args.length === 2) {
                return _toExpr(check(Z3.mk_store(contextPtr, array.ast, args[0].ast, args[1].ast)));
            }
            const _idxs = args.slice(0, args.length - 1).map(arg => arg.ast);
            return _toExpr(check(Z3.mk_store_n(contextPtr, array.ast, _idxs, args[args.length - 1].ast)));
        }
        class AstImpl {
            constructor(ptr) {
                this.ptr = ptr;
                this.ctx = ctx;
                const myAst = this.ast;
                Z3.inc_ref(contextPtr, myAst);
                cleanup.register(this, () => Z3.dec_ref(contextPtr, myAst));
            }
            get ast() {
                return this.ptr;
            }
            id() {
                return Z3.get_ast_id(contextPtr, this.ast);
            }
            eqIdentity(other) {
                _assertContext(other);
                return check(Z3.is_eq_ast(contextPtr, this.ast, other.ast));
            }
            neqIdentity(other) {
                _assertContext(other);
                return !this.eqIdentity(other);
            }
            sexpr() {
                return Z3.ast_to_string(contextPtr, this.ast);
            }
            hash() {
                return Z3.get_ast_hash(contextPtr, this.ast);
            }
            toString() {
                return this.sexpr();
            }
        }
        class SolverImpl {
            constructor(ptr = Z3.mk_solver(contextPtr)) {
                this.ctx = ctx;
                let myPtr;
                if (typeof ptr === 'string') {
                    myPtr = check(Z3.mk_solver_for_logic(contextPtr, _toSymbol(ptr)));
                }
                else {
                    myPtr = ptr;
                }
                this.ptr = myPtr;
                Z3.solver_inc_ref(contextPtr, myPtr);
                cleanup.register(this, () => Z3.solver_dec_ref(contextPtr, myPtr));
            }
            set(key, value) {
                Z3.solver_set_params(contextPtr, this.ptr, _toParams(key, value));
            }
            push() {
                Z3.solver_push(contextPtr, this.ptr);
            }
            pop(num = 1) {
                Z3.solver_pop(contextPtr, this.ptr, num);
            }
            numScopes() {
                return Z3.solver_get_num_scopes(contextPtr, this.ptr);
            }
            reset() {
                Z3.solver_reset(contextPtr, this.ptr);
            }
            add(...exprs) {
                _flattenArgs(exprs).forEach(expr => {
                    _assertContext(expr);
                    check(Z3.solver_assert(contextPtr, this.ptr, expr.ast));
                });
            }
            addAndTrack(expr, constant) {
                if (typeof constant === 'string') {
                    constant = Bool.const(constant);
                }
                (0, utils_1.assert)(isConst(constant), 'Provided expression that is not a constant to addAndTrack');
                check(Z3.solver_assert_and_track(contextPtr, this.ptr, expr.ast, constant.ast));
            }
            assertions() {
                return new AstVectorImpl(check(Z3.solver_get_assertions(contextPtr, this.ptr)));
            }
            async check(...exprs) {
                const assumptions = _flattenArgs(exprs).map(expr => {
                    _assertContext(expr);
                    return expr.ast;
                });
                const result = await asyncMutex.runExclusive(() => check(Z3.solver_check_assumptions(contextPtr, this.ptr, assumptions)));
                switch (result) {
                    case low_level_1.Z3_lbool.Z3_L_FALSE:
                        return 'unsat';
                    case low_level_1.Z3_lbool.Z3_L_TRUE:
                        return 'sat';
                    case low_level_1.Z3_lbool.Z3_L_UNDEF:
                        return 'unknown';
                    default:
                        (0, utils_1.assertExhaustive)(result);
                }
            }
            model() {
                return new ModelImpl(check(Z3.solver_get_model(contextPtr, this.ptr)));
            }
            toString() {
                return check(Z3.solver_to_string(contextPtr, this.ptr));
            }
            fromString(s) {
                Z3.solver_from_string(contextPtr, this.ptr, s);
                throwIfError();
            }
        }
        class OptimizeImpl {
            constructor(ptr = Z3.mk_optimize(contextPtr)) {
                this.ctx = ctx;
                let myPtr;
                myPtr = ptr;
                this.ptr = myPtr;
                Z3.optimize_inc_ref(contextPtr, myPtr);
                cleanup.register(this, () => Z3.optimize_dec_ref(contextPtr, myPtr));
            }
            set(key, value) {
                Z3.optimize_set_params(contextPtr, this.ptr, _toParams(key, value));
            }
            push() {
                Z3.optimize_push(contextPtr, this.ptr);
            }
            pop() {
                Z3.optimize_pop(contextPtr, this.ptr);
            }
            add(...exprs) {
                _flattenArgs(exprs).forEach(expr => {
                    _assertContext(expr);
                    check(Z3.optimize_assert(contextPtr, this.ptr, expr.ast));
                });
            }
            addSoft(expr, weight, id = "") {
                if (isCoercibleRational(weight)) {
                    weight = `${weight.numerator}/${weight.denominator}`;
                }
                check(Z3.optimize_assert_soft(contextPtr, this.ptr, expr.ast, weight.toString(), _toSymbol(id)));
            }
            addAndTrack(expr, constant) {
                if (typeof constant === 'string') {
                    constant = Bool.const(constant);
                }
                (0, utils_1.assert)(isConst(constant), 'Provided expression that is not a constant to addAndTrack');
                check(Z3.optimize_assert_and_track(contextPtr, this.ptr, expr.ast, constant.ast));
            }
            assertions() {
                return new AstVectorImpl(check(Z3.optimize_get_assertions(contextPtr, this.ptr)));
            }
            maximize(expr) {
                check(Z3.optimize_maximize(contextPtr, this.ptr, expr.ast));
            }
            minimize(expr) {
                check(Z3.optimize_minimize(contextPtr, this.ptr, expr.ast));
            }
            async check(...exprs) {
                const assumptions = _flattenArgs(exprs).map(expr => {
                    _assertContext(expr);
                    return expr.ast;
                });
                const result = await asyncMutex.runExclusive(() => check(Z3.optimize_check(contextPtr, this.ptr, assumptions)));
                switch (result) {
                    case low_level_1.Z3_lbool.Z3_L_FALSE:
                        return 'unsat';
                    case low_level_1.Z3_lbool.Z3_L_TRUE:
                        return 'sat';
                    case low_level_1.Z3_lbool.Z3_L_UNDEF:
                        return 'unknown';
                    default:
                        (0, utils_1.assertExhaustive)(result);
                }
            }
            model() {
                return new ModelImpl(check(Z3.optimize_get_model(contextPtr, this.ptr)));
            }
            toString() {
                return check(Z3.optimize_to_string(contextPtr, this.ptr));
            }
            fromString(s) {
                Z3.optimize_from_string(contextPtr, this.ptr, s);
                throwIfError();
            }
        }
        class ModelImpl {
            constructor(ptr = Z3.mk_model(contextPtr)) {
                this.ptr = ptr;
                this.ctx = ctx;
                Z3.model_inc_ref(contextPtr, ptr);
                cleanup.register(this, () => Z3.model_dec_ref(contextPtr, ptr));
            }
            length() {
                return Z3.model_get_num_consts(contextPtr, this.ptr) + Z3.model_get_num_funcs(contextPtr, this.ptr);
            }
            [Symbol.iterator]() {
                return this.values();
            }
            *entries() {
                const length = this.length();
                for (let i = 0; i < length; i++) {
                    yield [i, this.get(i)];
                }
            }
            *keys() {
                for (const [key] of this.entries()) {
                    yield key;
                }
            }
            *values() {
                for (const [, value] of this.entries()) {
                    yield value;
                }
            }
            decls() {
                return [...this.values()];
            }
            sexpr() {
                return check(Z3.model_to_string(contextPtr, this.ptr));
            }
            toString() {
                return this.sexpr();
            }
            eval(expr, modelCompletion = false) {
                _assertContext(expr);
                const r = check(Z3.model_eval(contextPtr, this.ptr, expr.ast, modelCompletion));
                if (r === null) {
                    throw new types_1.Z3Error('Failed to evaluate expression in the model');
                }
                return _toExpr(r);
            }
            get(i, to) {
                (0, utils_1.assert)(to === undefined || typeof i === 'number');
                if (typeof i === 'number') {
                    const length = this.length();
                    if (i >= length) {
                        throw new RangeError(`expected index ${i} to be less than length ${length}`);
                    }
                    if (to === undefined) {
                        const numConsts = check(Z3.model_get_num_consts(contextPtr, this.ptr));
                        if (i < numConsts) {
                            return new FuncDeclImpl(check(Z3.model_get_const_decl(contextPtr, this.ptr, i)));
                        }
                        else {
                            return new FuncDeclImpl(check(Z3.model_get_func_decl(contextPtr, this.ptr, i - numConsts)));
                        }
                    }
                    if (to < 0) {
                        to += length;
                    }
                    if (to >= length) {
                        throw new RangeError(`expected index ${to} to be less than length ${length}`);
                    }
                    const result = [];
                    for (let j = i; j < to; j++) {
                        result.push(this.get(j));
                    }
                    return result;
                }
                else if (isFuncDecl(i) || (isExpr(i) && isConst(i))) {
                    const result = this.getInterp(i);
                    (0, utils_1.assert)(result !== null);
                    return result;
                }
                else if (isSort(i)) {
                    return this.getUniverse(i);
                }
                (0, utils_1.assert)(false, 'Number, declaration or constant expected');
            }
            updateValue(decl, a) {
                _assertContext(decl);
                _assertContext(a);
                if (isExpr(decl)) {
                    decl = decl.decl();
                }
                if (isFuncDecl(decl) && decl.arity() !== 0 && isFuncInterp(a)) {
                    const funcInterp = this.addFuncInterp(decl, a.elseValue());
                    for (let i = 0; i < a.numEntries(); i++) {
                        const e = a.entry(i);
                        const n = e.numArgs();
                        const args = global.Array(n).map((_, i) => e.argValue(i));
                        funcInterp.addEntry(args, e.value());
                    }
                    return;
                }
                if (!isFuncDecl(decl) || decl.arity() !== 0) {
                    throw new types_1.Z3Error('Expecting 0-ary function or constant expression');
                }
                if (!isAst(a)) {
                    throw new types_1.Z3Error('Only func declarations can be assigned to func interpretations');
                }
                check(Z3.add_const_interp(contextPtr, this.ptr, decl.ptr, a.ast));
            }
            addFuncInterp(decl, defaultValue) {
                const fi = check(Z3.add_func_interp(contextPtr, this.ptr, decl.ptr, decl.range().cast(defaultValue).ptr));
                return new FuncInterpImpl(fi);
            }
            getInterp(expr) {
                (0, utils_1.assert)(isFuncDecl(expr) || isConst(expr), 'Declaration expected');
                if (isConst(expr)) {
                    (0, utils_1.assert)(isExpr(expr));
                    expr = expr.decl();
                }
                (0, utils_1.assert)(isFuncDecl(expr));
                if (expr.arity() === 0) {
                    const result = check(Z3.model_get_const_interp(contextPtr, this.ptr, expr.ptr));
                    if (result === null) {
                        return null;
                    }
                    return _toExpr(result);
                }
                else {
                    const interp = check(Z3.model_get_func_interp(contextPtr, this.ptr, expr.ptr));
                    if (interp === null) {
                        return null;
                    }
                    return new FuncInterpImpl(interp);
                }
            }
            getUniverse(sort) {
                _assertContext(sort);
                return new AstVectorImpl(check(Z3.model_get_sort_universe(contextPtr, this.ptr, sort.ptr)));
            }
        }
        class FuncEntryImpl {
            constructor(ptr) {
                this.ptr = ptr;
                this.ctx = ctx;
                Z3.func_entry_inc_ref(contextPtr, ptr);
                cleanup.register(this, () => Z3.func_entry_dec_ref(contextPtr, ptr));
            }
            numArgs() {
                return check(Z3.func_entry_get_num_args(contextPtr, this.ptr));
            }
            argValue(i) {
                return _toExpr(check(Z3.func_entry_get_arg(contextPtr, this.ptr, i)));
            }
            value() {
                return _toExpr(check(Z3.func_entry_get_value(contextPtr, this.ptr)));
            }
        }
        class FuncInterpImpl {
            constructor(ptr) {
                this.ptr = ptr;
                this.ctx = ctx;
                Z3.func_interp_inc_ref(contextPtr, ptr);
                cleanup.register(this, () => Z3.func_interp_dec_ref(contextPtr, ptr));
            }
            elseValue() {
                return _toExpr(check(Z3.func_interp_get_else(contextPtr, this.ptr)));
            }
            numEntries() {
                return check(Z3.func_interp_get_num_entries(contextPtr, this.ptr));
            }
            arity() {
                return check(Z3.func_interp_get_arity(contextPtr, this.ptr));
            }
            entry(i) {
                return new FuncEntryImpl(check(Z3.func_interp_get_entry(contextPtr, this.ptr, i)));
            }
            addEntry(args, value) {
                const argsVec = new AstVectorImpl();
                for (const arg of args) {
                    argsVec.push(arg);
                }
                _assertContext(argsVec);
                _assertContext(value);
                (0, utils_1.assert)(this.arity() === argsVec.length(), "Number of arguments in entry doesn't match function arity");
                check(Z3.func_interp_add_entry(contextPtr, this.ptr, argsVec.ptr, value.ptr));
            }
        }
        class SortImpl extends AstImpl {
            get ast() {
                return Z3.sort_to_ast(contextPtr, this.ptr);
            }
            kind() {
                return Z3.get_sort_kind(contextPtr, this.ptr);
            }
            subsort(other) {
                _assertContext(other);
                return false;
            }
            cast(expr) {
                _assertContext(expr);
                (0, utils_1.assert)(expr.sort.eqIdentity(expr.sort), 'Sort mismatch');
                return expr;
            }
            name() {
                return _fromSymbol(Z3.get_sort_name(contextPtr, this.ptr));
            }
            eqIdentity(other) {
                _assertContext(other);
                return check(Z3.is_eq_sort(contextPtr, this.ptr, other.ptr));
            }
            neqIdentity(other) {
                return !this.eqIdentity(other);
            }
        }
        class FuncDeclImpl extends AstImpl {
            get ast() {
                return Z3.func_decl_to_ast(contextPtr, this.ptr);
            }
            name() {
                return _fromSymbol(Z3.get_decl_name(contextPtr, this.ptr));
            }
            arity() {
                return Z3.get_arity(contextPtr, this.ptr);
            }
            domain(i) {
                (0, utils_1.assert)(i < this.arity(), 'Index out of bounds');
                return _toSort(Z3.get_domain(contextPtr, this.ptr, i));
            }
            range() {
                return _toSort(Z3.get_range(contextPtr, this.ptr));
            }
            kind() {
                return Z3.get_decl_kind(contextPtr, this.ptr);
            }
            params() {
                const n = Z3.get_decl_num_parameters(contextPtr, this.ptr);
                const result = [];
                for (let i = 0; i < n; i++) {
                    const kind = check(Z3.get_decl_parameter_kind(contextPtr, this.ptr, i));
                    switch (kind) {
                        case low_level_1.Z3_parameter_kind.Z3_PARAMETER_INT:
                            result.push(check(Z3.get_decl_int_parameter(contextPtr, this.ptr, i)));
                            break;
                        case low_level_1.Z3_parameter_kind.Z3_PARAMETER_DOUBLE:
                            result.push(check(Z3.get_decl_double_parameter(contextPtr, this.ptr, i)));
                            break;
                        case low_level_1.Z3_parameter_kind.Z3_PARAMETER_RATIONAL:
                            result.push(check(Z3.get_decl_rational_parameter(contextPtr, this.ptr, i)));
                            break;
                        case low_level_1.Z3_parameter_kind.Z3_PARAMETER_SYMBOL:
                            result.push(_fromSymbol(check(Z3.get_decl_symbol_parameter(contextPtr, this.ptr, i))));
                            break;
                        case low_level_1.Z3_parameter_kind.Z3_PARAMETER_SORT:
                            result.push(new SortImpl(check(Z3.get_decl_sort_parameter(contextPtr, this.ptr, i))));
                            break;
                        case low_level_1.Z3_parameter_kind.Z3_PARAMETER_AST:
                            result.push(new ExprImpl(check(Z3.get_decl_ast_parameter(contextPtr, this.ptr, i))));
                            break;
                        case low_level_1.Z3_parameter_kind.Z3_PARAMETER_FUNC_DECL:
                            result.push(new FuncDeclImpl(check(Z3.get_decl_func_decl_parameter(contextPtr, this.ptr, i))));
                            break;
                        default:
                            (0, utils_1.assertExhaustive)(kind);
                    }
                }
                return result;
            }
            call(...args) {
                (0, utils_1.assert)(args.length === this.arity(), `Incorrect number of arguments to ${this}`);
                return _toExpr(check(Z3.mk_app(contextPtr, this.ptr, args.map((arg, i) => {
                    return this.domain(i).cast(arg).ast;
                }))));
            }
        }
        class ExprImpl extends AstImpl {
            get sort() {
                return _toSort(Z3.get_sort(contextPtr, this.ast));
            }
            eq(other) {
                return new BoolImpl(check(Z3.mk_eq(contextPtr, this.ast, from(other).ast)));
            }
            neq(other) {
                return new BoolImpl(check(Z3.mk_distinct(contextPtr, [this, other].map(expr => from(expr).ast))));
            }
            name() {
                return this.decl().name();
            }
            params() {
                return this.decl().params();
            }
            decl() {
                (0, utils_1.assert)(isApp(this), 'Z3 application expected');
                return new FuncDeclImpl(check(Z3.get_app_decl(contextPtr, check(Z3.to_app(contextPtr, this.ast)))));
            }
            numArgs() {
                (0, utils_1.assert)(isApp(this), 'Z3 applicaiton expected');
                return check(Z3.get_app_num_args(contextPtr, check(Z3.to_app(contextPtr, this.ast))));
            }
            arg(i) {
                (0, utils_1.assert)(isApp(this), 'Z3 applicaiton expected');
                (0, utils_1.assert)(i < this.numArgs(), `Invalid argument index - expected ${i} to be less than ${this.numArgs()}`);
                return _toExpr(check(Z3.get_app_arg(contextPtr, check(Z3.to_app(contextPtr, this.ast)), i)));
            }
            children() {
                const num_args = this.numArgs();
                if (isApp(this)) {
                    const result = [];
                    for (let i = 0; i < num_args; i++) {
                        result.push(this.arg(i));
                    }
                    return result;
                }
                return [];
            }
        }
        class PatternImpl {
            constructor(ptr) {
                this.ptr = ptr;
                this.ctx = ctx;
                // TODO: implement rest of Pattern
            }
        }
        class BoolSortImpl extends SortImpl {
            cast(other) {
                if (typeof other === 'boolean') {
                    other = Bool.val(other);
                }
                (0, utils_1.assert)(isExpr(other), 'true, false or Z3 Boolean expression expected.');
                (0, utils_1.assert)(this.eqIdentity(other.sort), 'Value cannot be converted into a Z3 Boolean value');
                return other;
            }
            subsort(other) {
                _assertContext(other.ctx);
                return other instanceof ArithSortImpl;
            }
        }
        class BoolImpl extends ExprImpl {
            not() {
                return Not(this);
            }
            and(other) {
                return And(this, other);
            }
            or(other) {
                return Or(this, other);
            }
            xor(other) {
                return Xor(this, other);
            }
            implies(other) {
                return Implies(this, other);
            }
            iff(other) {
                return Iff(this, other);
            }
        }
        class ProbeImpl {
            constructor(ptr) {
                this.ptr = ptr;
                this.ctx = ctx;
            }
        }
        class TacticImpl {
            constructor(tactic) {
                this.ctx = ctx;
                let myPtr;
                if (typeof tactic === 'string') {
                    myPtr = check(Z3.mk_tactic(contextPtr, tactic));
                }
                else {
                    myPtr = tactic;
                }
                this.ptr = myPtr;
                Z3.tactic_inc_ref(contextPtr, myPtr);
                cleanup.register(this, () => Z3.tactic_dec_ref(contextPtr, myPtr));
            }
        }
        class ArithSortImpl extends SortImpl {
            cast(other) {
                const sortTypeStr = isIntSort(this) ? 'IntSort' : 'RealSort';
                if (isExpr(other)) {
                    const otherS = other.sort;
                    if (isArith(other)) {
                        if (this.eqIdentity(otherS)) {
                            return other;
                        }
                        else if (isIntSort(otherS) && isRealSort(this)) {
                            return ToReal(other);
                        }
                        (0, utils_1.assert)(false, "Can't cast Real to IntSort without loss");
                    }
                    else if (isBool(other)) {
                        if (isIntSort(this)) {
                            return If(other, 1, 0);
                        }
                        else {
                            return ToReal(If(other, 1, 0));
                        }
                    }
                    (0, utils_1.assert)(false, `Can't cast expression to ${sortTypeStr}`);
                }
                else {
                    if (typeof other !== 'boolean') {
                        if (isIntSort(this)) {
                            (0, utils_1.assert)(!isCoercibleRational(other), "Can't cast fraction to IntSort");
                            return Int.val(other);
                        }
                        return Real.val(other);
                    }
                    (0, utils_1.assert)(false, `Can't cast primitive to ${sortTypeStr}`);
                }
            }
        }
        function Sum(arg0, ...args) {
            if (arg0 instanceof BitVecImpl) {
                // Assert only 2
                if (args.length !== 1) {
                    throw new Error('BitVec add only supports 2 arguments');
                }
                return new BitVecImpl(check(Z3.mk_bvadd(contextPtr, arg0.ast, arg0.sort.cast(args[0]).ast)));
            }
            else {
                (0, utils_1.assert)(arg0 instanceof ArithImpl);
                return new ArithImpl(check(Z3.mk_add(contextPtr, [arg0.ast].concat(args.map(arg => arg0.sort.cast(arg).ast)))));
            }
        }
        function Sub(arg0, ...args) {
            if (arg0 instanceof BitVecImpl) {
                // Assert only 2
                if (args.length !== 1) {
                    throw new Error('BitVec sub only supports 2 arguments');
                }
                return new BitVecImpl(check(Z3.mk_bvsub(contextPtr, arg0.ast, arg0.sort.cast(args[0]).ast)));
            }
            else {
                (0, utils_1.assert)(arg0 instanceof ArithImpl);
                return new ArithImpl(check(Z3.mk_sub(contextPtr, [arg0.ast].concat(args.map(arg => arg0.sort.cast(arg).ast)))));
            }
        }
        function Product(arg0, ...args) {
            if (arg0 instanceof BitVecImpl) {
                // Assert only 2
                if (args.length !== 1) {
                    throw new Error('BitVec mul only supports 2 arguments');
                }
                return new BitVecImpl(check(Z3.mk_bvmul(contextPtr, arg0.ast, arg0.sort.cast(args[0]).ast)));
            }
            else {
                (0, utils_1.assert)(arg0 instanceof ArithImpl);
                return new ArithImpl(check(Z3.mk_mul(contextPtr, [arg0.ast].concat(args.map(arg => arg0.sort.cast(arg).ast)))));
            }
        }
        function Div(arg0, arg1) {
            if (arg0 instanceof BitVecImpl) {
                return new BitVecImpl(check(Z3.mk_bvsdiv(contextPtr, arg0.ast, arg0.sort.cast(arg1).ast)));
            }
            else {
                (0, utils_1.assert)(arg0 instanceof ArithImpl);
                return new ArithImpl(check(Z3.mk_div(contextPtr, arg0.ast, arg0.sort.cast(arg1).ast)));
            }
        }
        function BUDiv(arg0, arg1) {
            return new BitVecImpl(check(Z3.mk_bvudiv(contextPtr, arg0.ast, arg0.sort.cast(arg1).ast)));
        }
        function Neg(a) {
            if (a instanceof BitVecImpl) {
                return new BitVecImpl(check(Z3.mk_bvneg(contextPtr, a.ast)));
            }
            else {
                (0, utils_1.assert)(a instanceof ArithImpl);
                return new ArithImpl(check(Z3.mk_unary_minus(contextPtr, a.ast)));
            }
        }
        function Mod(a, b) {
            if (a instanceof BitVecImpl) {
                return new BitVecImpl(check(Z3.mk_bvsrem(contextPtr, a.ast, a.sort.cast(b).ast)));
            }
            else {
                (0, utils_1.assert)(a instanceof ArithImpl);
                return new ArithImpl(check(Z3.mk_mod(contextPtr, a.ast, a.sort.cast(b).ast)));
            }
        }
        class ArithImpl extends ExprImpl {
            add(other) {
                return Sum(this, other);
            }
            mul(other) {
                return Product(this, other);
            }
            sub(other) {
                return Sub(this, other);
            }
            pow(exponent) {
                return new ArithImpl(check(Z3.mk_power(contextPtr, this.ast, this.sort.cast(exponent).ast)));
            }
            div(other) {
                return Div(this, other);
            }
            mod(other) {
                return Mod(this, other);
            }
            neg() {
                return Neg(this);
            }
            le(other) {
                return LE(this, other);
            }
            lt(other) {
                return LT(this, other);
            }
            gt(other) {
                return GT(this, other);
            }
            ge(other) {
                return GE(this, other);
            }
        }
        class IntNumImpl extends ArithImpl {
            value() {
                return BigInt(this.asString());
            }
            asString() {
                return Z3.get_numeral_string(contextPtr, this.ast);
            }
            asBinary() {
                return Z3.get_numeral_binary_string(contextPtr, this.ast);
            }
        }
        class RatNumImpl extends ArithImpl {
            value() {
                return { numerator: this.numerator().value(), denominator: this.denominator().value() };
            }
            numerator() {
                return new IntNumImpl(Z3.get_numerator(contextPtr, this.ast));
            }
            denominator() {
                return new IntNumImpl(Z3.get_denominator(contextPtr, this.ast));
            }
            asNumber() {
                const { numerator, denominator } = this.value();
                const div = numerator / denominator;
                return Number(div) + Number(numerator - div * denominator) / Number(denominator);
            }
            asDecimal(prec = Number.parseInt(getParam('precision') ?? FALLBACK_PRECISION.toString())) {
                return Z3.get_numeral_decimal_string(contextPtr, this.ast, prec);
            }
            asString() {
                return Z3.get_numeral_string(contextPtr, this.ast);
            }
        }
        class BitVecSortImpl extends SortImpl {
            size() {
                return Z3.get_bv_sort_size(contextPtr, this.ptr);
            }
            subsort(other) {
                return isBitVecSort(other) && this.size() < other.size();
            }
            cast(other) {
                if (isExpr(other)) {
                    _assertContext(other);
                    return other;
                }
                (0, utils_1.assert)(!isCoercibleRational(other), "Can't convert rational to BitVec");
                return BitVec.val(other, this.size());
            }
        }
        class BitVecImpl extends ExprImpl {
            size() {
                return this.sort.size();
            }
            add(other) {
                return Sum(this, other);
            }
            mul(other) {
                return Product(this, other);
            }
            sub(other) {
                return Sub(this, other);
            }
            sdiv(other) {
                return Div(this, other);
            }
            udiv(other) {
                return BUDiv(this, other);
            }
            smod(other) {
                return Mod(this, other);
            }
            urem(other) {
                return new BitVecImpl(check(Z3.mk_bvurem(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            srem(other) {
                return new BitVecImpl(check(Z3.mk_bvsrem(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            neg() {
                return Neg(this);
            }
            or(other) {
                return new BitVecImpl(check(Z3.mk_bvor(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            and(other) {
                return new BitVecImpl(check(Z3.mk_bvand(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            nand(other) {
                return new BitVecImpl(check(Z3.mk_bvnand(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            xor(other) {
                return new BitVecImpl(check(Z3.mk_bvxor(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            xnor(other) {
                return new BitVecImpl(check(Z3.mk_bvxnor(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            shr(count) {
                return new BitVecImpl(check(Z3.mk_bvashr(contextPtr, this.ast, this.sort.cast(count).ast)));
            }
            lshr(count) {
                return new BitVecImpl(check(Z3.mk_bvlshr(contextPtr, this.ast, this.sort.cast(count).ast)));
            }
            shl(count) {
                return new BitVecImpl(check(Z3.mk_bvshl(contextPtr, this.ast, this.sort.cast(count).ast)));
            }
            rotateRight(count) {
                return new BitVecImpl(check(Z3.mk_ext_rotate_right(contextPtr, this.ast, this.sort.cast(count).ast)));
            }
            rotateLeft(count) {
                return new BitVecImpl(check(Z3.mk_ext_rotate_left(contextPtr, this.ast, this.sort.cast(count).ast)));
            }
            not() {
                return new BitVecImpl(check(Z3.mk_bvnot(contextPtr, this.ast)));
            }
            extract(high, low) {
                return Extract(high, low, this);
            }
            signExt(count) {
                return new BitVecImpl(check(Z3.mk_sign_ext(contextPtr, count, this.ast)));
            }
            zeroExt(count) {
                return new BitVecImpl(check(Z3.mk_zero_ext(contextPtr, count, this.ast)));
            }
            repeat(count) {
                return new BitVecImpl(check(Z3.mk_repeat(contextPtr, count, this.ast)));
            }
            sle(other) {
                return SLE(this, other);
            }
            ule(other) {
                return ULE(this, other);
            }
            slt(other) {
                return SLT(this, other);
            }
            ult(other) {
                return ULT(this, other);
            }
            sge(other) {
                return SGE(this, other);
            }
            uge(other) {
                return UGE(this, other);
            }
            sgt(other) {
                return SGT(this, other);
            }
            ugt(other) {
                return UGT(this, other);
            }
            redAnd() {
                return new BitVecImpl(check(Z3.mk_bvredand(contextPtr, this.ast)));
            }
            redOr() {
                return new BitVecImpl(check(Z3.mk_bvredor(contextPtr, this.ast)));
            }
            addNoOverflow(other, isSigned) {
                return new BoolImpl(check(Z3.mk_bvadd_no_overflow(contextPtr, this.ast, this.sort.cast(other).ast, isSigned)));
            }
            addNoUnderflow(other) {
                return new BoolImpl(check(Z3.mk_bvadd_no_underflow(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            subNoOverflow(other) {
                return new BoolImpl(check(Z3.mk_bvsub_no_overflow(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            subNoUndeflow(other, isSigned) {
                return new BoolImpl(check(Z3.mk_bvsub_no_underflow(contextPtr, this.ast, this.sort.cast(other).ast, isSigned)));
            }
            sdivNoOverflow(other) {
                return new BoolImpl(check(Z3.mk_bvsdiv_no_overflow(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            mulNoOverflow(other, isSigned) {
                return new BoolImpl(check(Z3.mk_bvmul_no_overflow(contextPtr, this.ast, this.sort.cast(other).ast, isSigned)));
            }
            mulNoUndeflow(other) {
                return new BoolImpl(check(Z3.mk_bvmul_no_underflow(contextPtr, this.ast, this.sort.cast(other).ast)));
            }
            negNoOverflow() {
                return new BoolImpl(check(Z3.mk_bvneg_no_overflow(contextPtr, this.ast)));
            }
        }
        class BitVecNumImpl extends BitVecImpl {
            value() {
                return BigInt(this.asString());
            }
            asSignedValue() {
                let val = this.value();
                const size = BigInt(this.size());
                if (val >= 2n ** (size - 1n)) {
                    val = val - 2n ** size;
                }
                if (val < (-2n) ** (size - 1n)) {
                    val = val + 2n ** size;
                }
                return val;
            }
            asString() {
                return Z3.get_numeral_string(contextPtr, this.ast);
            }
            asBinaryString() {
                return Z3.get_numeral_binary_string(contextPtr, this.ast);
            }
        }
        class ArraySortImpl extends SortImpl {
            domain() {
                return _toSort(check(Z3.get_array_sort_domain(contextPtr, this.ptr)));
            }
            domain_n(i) {
                return _toSort(check(Z3.get_array_sort_domain_n(contextPtr, this.ptr, i)));
            }
            range() {
                return _toSort(check(Z3.get_array_sort_range(contextPtr, this.ptr)));
            }
        }
        class ArrayImpl extends ExprImpl {
            domain() {
                return this.sort.domain();
            }
            domain_n(i) {
                return this.sort.domain_n(i);
            }
            range() {
                return this.sort.range();
            }
            select(...indices) {
                return Select(this, ...indices);
            }
            store(...indicesAndValue) {
                return Store(this, ...indicesAndValue);
            }
        }
        class QuantifierImpl extends ExprImpl {
            is_forall() {
                return Z3.is_quantifier_forall(contextPtr, this.ast);
            }
            is_exists() {
                return Z3.is_quantifier_exists(contextPtr, this.ast);
            }
            is_lambda() {
                return Z3.is_lambda(contextPtr, this.ast);
            }
            weight() {
                return Z3.get_quantifier_weight(contextPtr, this.ast);
            }
            num_patterns() {
                return Z3.get_quantifier_num_patterns(contextPtr, this.ast);
            }
            pattern(i) {
                return new PatternImpl(check(Z3.get_quantifier_pattern_ast(contextPtr, this.ast, i)));
            }
            num_no_patterns() {
                return Z3.get_quantifier_num_no_patterns(contextPtr, this.ast);
            }
            no_pattern(i) {
                return _toExpr(check(Z3.get_quantifier_no_pattern_ast(contextPtr, this.ast, i)));
            }
            body() {
                return _toExpr(check(Z3.get_quantifier_body(contextPtr, this.ast)));
            }
            num_vars() {
                return Z3.get_quantifier_num_bound(contextPtr, this.ast);
            }
            var_name(i) {
                return _fromSymbol(Z3.get_quantifier_bound_name(contextPtr, this.ast, i));
            }
            var_sort(i) {
                return _toSort(check(Z3.get_quantifier_bound_sort(contextPtr, this.ast, i)));
            }
            children() {
                return [this.body()];
            }
        }
        class NonLambdaQuantifierImpl extends QuantifierImpl {
            not() {
                return Not(this);
            }
            and(other) {
                return And(this, other);
            }
            or(other) {
                return Or(this, other);
            }
            xor(other) {
                return Xor(this, other);
            }
            implies(other) {
                return Implies(this, other);
            }
            iff(other) {
                return Iff(this, other);
            }
        }
        // isBool will return false which is unlike the python API (but like the C API)
        class LambdaImpl extends QuantifierImpl {
            domain() {
                return this.sort.domain();
            }
            domain_n(i) {
                return this.sort.domain_n(i);
            }
            range() {
                return this.sort.range();
            }
            select(...indices) {
                return Select(this, ...indices);
            }
            store(...indicesAndValue) {
                return Store(this, ...indicesAndValue);
            }
        }
        class AstVectorImpl {
            constructor(ptr = Z3.mk_ast_vector(contextPtr)) {
                this.ptr = ptr;
                this.ctx = ctx;
                Z3.ast_vector_inc_ref(contextPtr, ptr);
                cleanup.register(this, () => Z3.ast_vector_dec_ref(contextPtr, ptr));
            }
            length() {
                return Z3.ast_vector_size(contextPtr, this.ptr);
            }
            [Symbol.iterator]() {
                return this.values();
            }
            *entries() {
                const length = this.length();
                for (let i = 0; i < length; i++) {
                    yield [i, this.get(i)];
                }
            }
            *keys() {
                for (let [key] of this.entries()) {
                    yield key;
                }
            }
            *values() {
                for (let [, value] of this.entries()) {
                    yield value;
                }
            }
            get(from, to) {
                const length = this.length();
                if (from < 0) {
                    from += length;
                }
                if (from >= length) {
                    throw new RangeError(`expected from index ${from} to be less than length ${length}`);
                }
                if (to === undefined) {
                    return _toAst(check(Z3.ast_vector_get(contextPtr, this.ptr, from)));
                }
                if (to < 0) {
                    to += length;
                }
                if (to >= length) {
                    throw new RangeError(`expected to index ${to} to be less than length ${length}`);
                }
                const result = [];
                for (let i = from; i < to; i++) {
                    result.push(_toAst(check(Z3.ast_vector_get(contextPtr, this.ptr, i))));
                }
                return result;
            }
            set(i, v) {
                _assertContext(v);
                if (i >= this.length()) {
                    throw new RangeError(`expected index ${i} to be less than length ${this.length()}`);
                }
                check(Z3.ast_vector_set(contextPtr, this.ptr, i, v.ast));
            }
            push(v) {
                _assertContext(v);
                check(Z3.ast_vector_push(contextPtr, this.ptr, v.ast));
            }
            resize(size) {
                check(Z3.ast_vector_resize(contextPtr, this.ptr, size));
            }
            has(v) {
                _assertContext(v);
                for (const item of this.values()) {
                    if (item.eqIdentity(v)) {
                        return true;
                    }
                }
                return false;
            }
            sexpr() {
                return check(Z3.ast_vector_to_string(contextPtr, this.ptr));
            }
        }
        class AstMapImpl {
            constructor(ptr = Z3.mk_ast_map(contextPtr)) {
                this.ptr = ptr;
                this.ctx = ctx;
                Z3.ast_map_inc_ref(contextPtr, ptr);
                cleanup.register(this, () => Z3.ast_map_dec_ref(contextPtr, ptr));
            }
            [Symbol.iterator]() {
                return this.entries();
            }
            get size() {
                return Z3.ast_map_size(contextPtr, this.ptr);
            }
            *entries() {
                for (const key of this.keys()) {
                    yield [key, this.get(key)];
                }
            }
            keys() {
                return new AstVectorImpl(Z3.ast_map_keys(contextPtr, this.ptr));
            }
            *values() {
                for (const [_, value] of this.entries()) {
                    yield value;
                }
            }
            get(key) {
                return _toAst(check(Z3.ast_map_find(contextPtr, this.ptr, key.ast)));
            }
            set(key, value) {
                check(Z3.ast_map_insert(contextPtr, this.ptr, key.ast, value.ast));
            }
            delete(key) {
                check(Z3.ast_map_erase(contextPtr, this.ptr, key.ast));
            }
            clear() {
                check(Z3.ast_map_reset(contextPtr, this.ptr));
            }
            has(key) {
                return check(Z3.ast_map_contains(contextPtr, this.ptr, key.ast));
            }
            sexpr() {
                return check(Z3.ast_map_to_string(contextPtr, this.ptr));
            }
        }
        function substitute(t, ...substitutions) {
            _assertContext(t);
            const from = [];
            const to = [];
            for (const [f, t] of substitutions) {
                _assertContext(f);
                _assertContext(t);
                from.push(f.ast);
                to.push(t.ast);
            }
            return _toExpr(check(Z3.substitute(contextPtr, t.ast, from, to)));
        }
        function ast_from_string(s) {
            const sort_names = [];
            const sorts = [];
            const decl_names = [];
            const decls = [];
            const v = new AstVectorImpl(check(Z3.parse_smtlib2_string(contextPtr, s, sort_names, sorts, decl_names, decls)));
            if (v.length() !== 1) {
                throw new Error('Expected exactly one AST. Instead got ' + v.length() + ': ' + v.sexpr());
            }
            return v.get(0);
        }
        const ctx = {
            ptr: contextPtr,
            name,
            /////////////
            // Classes //
            /////////////
            Solver: SolverImpl,
            Optimize: OptimizeImpl,
            Model: ModelImpl,
            Tactic: TacticImpl,
            AstVector: AstVectorImpl,
            AstMap: AstMapImpl,
            ///////////////
            // Functions //
            ///////////////
            interrupt,
            isModel,
            isAst,
            isSort,
            isFuncDecl,
            isFuncInterp,
            isApp,
            isConst,
            isExpr,
            isVar,
            isAppOf,
            isBool,
            isTrue,
            isFalse,
            isAnd,
            isOr,
            isImplies,
            isNot,
            isEq,
            isDistinct,
            isQuantifier,
            isArith,
            isArithSort,
            isInt,
            isIntVal,
            isIntSort,
            isReal,
            isRealVal,
            isRealSort,
            isBitVecSort,
            isBitVec,
            isBitVecVal,
            isArraySort,
            isArray,
            isConstArray,
            isProbe,
            isTactic,
            isAstVector,
            eqIdentity,
            getVarIndex,
            from,
            solve,
            /////////////
            // Objects //
            /////////////
            Sort,
            Function,
            RecFunc,
            Bool,
            Int,
            Real,
            BitVec,
            Array,
            ////////////////
            // Operations //
            ////////////////
            If,
            Distinct,
            Const,
            Consts,
            FreshConst,
            Var,
            Implies,
            Iff,
            Eq,
            Xor,
            Not,
            And,
            Or,
            ForAll,
            Exists,
            Lambda,
            ToReal,
            ToInt,
            IsInt,
            Sqrt,
            Cbrt,
            BV2Int,
            Int2BV,
            Concat,
            Cond,
            LT,
            GT,
            LE,
            GE,
            ULT,
            UGT,
            ULE,
            UGE,
            SLT,
            SGT,
            SLE,
            SGE,
            Sum,
            Sub,
            Product,
            Div,
            BUDiv,
            Neg,
            Mod,
            Select,
            Store,
            Extract,
            substitute,
            simplify,
            /////////////
            // Loading //
            /////////////
            ast_from_string,
        };
        cleanup.register(ctx, () => Z3.del_context(contextPtr));
        return ctx;
    }
    return {
        enableTrace,
        disableTrace,
        getVersion,
        getVersionString,
        getFullVersion,
        openLog,
        appendLog,
        getParam,
        setParam,
        resetParams,
        Context: createContext,
    };
}
exports.createApi = createApi;

}).call(this)}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})
},{"../low-level":14,"./types":12,"./utils":13,"async-mutex":5}],11:[function(require,module,exports){
"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __exportStar = (this && this.__exportStar) || function(m, exports) {
    for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);
};
Object.defineProperty(exports, "__esModule", { value: true });
__exportStar(require("./high-level"), exports);
__exportStar(require("./types"), exports);

},{"./high-level":10,"./types":12}],12:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.Z3AssertionError = exports.Z3Error = void 0;
/**
 * Used to create a Real constant
 *
 * ```typescript
 * const x = from({ numerator: 1, denominator: 3 })
 *
 * x
 * // 1/3
 * isReal(x)
 * // true
 * isRealVal(x)
 * // true
 * x.asNumber()
 * // 0.3333333333333333
 * ```
 * @see {@link Context.from}
 * @category Global
 */
class Z3Error extends Error {
}
exports.Z3Error = Z3Error;
class Z3AssertionError extends Z3Error {
}
exports.Z3AssertionError = Z3AssertionError;

},{}],13:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.allSatisfy = exports.assert = exports.assertExhaustive = void 0;
const types_1 = require("./types");
function getAllProperties(obj) {
    const properties = new Set();
    do {
        for (const key of Reflect.ownKeys(obj)) {
            properties.add([obj, key]);
        }
    } while ((obj = Reflect.getPrototypeOf(obj)) && obj !== Object.prototype);
    return properties;
}
/**
 * Use to ensure that switches are checked to be exhaustive at compile time
 *
 * @example Basic usage
 * ```typescript
 * enum Something {
 *  left,
 *  right,
 * };
 * const something = getSomething();
 * switch (something) {
 *  case Something.left:
 *    ...
 *  case Something.right:
 *    ...
 *  default:
 *    assertExhaustive(something);
 * }
 * ```
 *
 * @param x - The param on which the switch operates
 */
function assertExhaustive(x) {
    throw new Error('Unexpected code execution detected, should be caught at compile time');
}
exports.assertExhaustive = assertExhaustive;
function assert(condition, reason) {
    if (!condition) {
        throw new types_1.Z3AssertionError(reason ?? 'Assertion failed');
    }
}
exports.assert = assert;
/**
 * Check the all elements of a `collection` satisfy the `premise`.
 * If any of the items fail the `premise`, returns false;
 * @returns null if the `collection` is empty, boolean otherwise
 */
function allSatisfy(collection, premise) {
    let hasItems = false;
    for (const arg of collection) {
        hasItems = true;
        if (!premise(arg)) {
            return false;
        }
    }
    return hasItems === true ? true : null;
}
exports.allSatisfy = allSatisfy;

},{"./types":12}],14:[function(require,module,exports){
"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __exportStar = (this && this.__exportStar) || function(m, exports) {
    for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);
};
Object.defineProperty(exports, "__esModule", { value: true });
__exportStar(require("./types.__GENERATED__"), exports);
__exportStar(require("./wrapper.__GENERATED__"), exports);

},{"./types.__GENERATED__":15,"./wrapper.__GENERATED__":16}],15:[function(require,module,exports){
"use strict";
// THIS FILE IS AUTOMATICALLY GENERATED BY make-ts-wrapper.ts
// DO NOT EDIT IT BY HAND
Object.defineProperty(exports, "__esModule", { value: true });
exports.Z3_goal_prec = exports.Z3_error_code = exports.Z3_ast_print_mode = exports.Z3_param_kind = exports.Z3_decl_kind = exports.Z3_ast_kind = exports.Z3_sort_kind = exports.Z3_parameter_kind = exports.Z3_symbol_kind = exports.Z3_lbool = void 0;
var Z3_lbool;
(function (Z3_lbool) {
    Z3_lbool[Z3_lbool["Z3_L_FALSE"] = -1] = "Z3_L_FALSE";
    Z3_lbool[Z3_lbool["Z3_L_UNDEF"] = 0] = "Z3_L_UNDEF";
    Z3_lbool[Z3_lbool["Z3_L_TRUE"] = 1] = "Z3_L_TRUE";
})(Z3_lbool = exports.Z3_lbool || (exports.Z3_lbool = {}));
var Z3_symbol_kind;
(function (Z3_symbol_kind) {
    Z3_symbol_kind[Z3_symbol_kind["Z3_INT_SYMBOL"] = 0] = "Z3_INT_SYMBOL";
    Z3_symbol_kind[Z3_symbol_kind["Z3_STRING_SYMBOL"] = 1] = "Z3_STRING_SYMBOL";
})(Z3_symbol_kind = exports.Z3_symbol_kind || (exports.Z3_symbol_kind = {}));
var Z3_parameter_kind;
(function (Z3_parameter_kind) {
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_INT"] = 0] = "Z3_PARAMETER_INT";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_DOUBLE"] = 1] = "Z3_PARAMETER_DOUBLE";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_RATIONAL"] = 2] = "Z3_PARAMETER_RATIONAL";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_SYMBOL"] = 3] = "Z3_PARAMETER_SYMBOL";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_SORT"] = 4] = "Z3_PARAMETER_SORT";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_AST"] = 5] = "Z3_PARAMETER_AST";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_FUNC_DECL"] = 6] = "Z3_PARAMETER_FUNC_DECL";
})(Z3_parameter_kind = exports.Z3_parameter_kind || (exports.Z3_parameter_kind = {}));
var Z3_sort_kind;
(function (Z3_sort_kind) {
    Z3_sort_kind[Z3_sort_kind["Z3_UNINTERPRETED_SORT"] = 0] = "Z3_UNINTERPRETED_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_BOOL_SORT"] = 1] = "Z3_BOOL_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_INT_SORT"] = 2] = "Z3_INT_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_REAL_SORT"] = 3] = "Z3_REAL_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_BV_SORT"] = 4] = "Z3_BV_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_ARRAY_SORT"] = 5] = "Z3_ARRAY_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_DATATYPE_SORT"] = 6] = "Z3_DATATYPE_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_RELATION_SORT"] = 7] = "Z3_RELATION_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_FINITE_DOMAIN_SORT"] = 8] = "Z3_FINITE_DOMAIN_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_FLOATING_POINT_SORT"] = 9] = "Z3_FLOATING_POINT_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_ROUNDING_MODE_SORT"] = 10] = "Z3_ROUNDING_MODE_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_SEQ_SORT"] = 11] = "Z3_SEQ_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_RE_SORT"] = 12] = "Z3_RE_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_CHAR_SORT"] = 13] = "Z3_CHAR_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_TYPE_VAR"] = 14] = "Z3_TYPE_VAR";
    Z3_sort_kind[Z3_sort_kind["Z3_UNKNOWN_SORT"] = 1000] = "Z3_UNKNOWN_SORT";
})(Z3_sort_kind = exports.Z3_sort_kind || (exports.Z3_sort_kind = {}));
var Z3_ast_kind;
(function (Z3_ast_kind) {
    Z3_ast_kind[Z3_ast_kind["Z3_NUMERAL_AST"] = 0] = "Z3_NUMERAL_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_APP_AST"] = 1] = "Z3_APP_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_VAR_AST"] = 2] = "Z3_VAR_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_QUANTIFIER_AST"] = 3] = "Z3_QUANTIFIER_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_SORT_AST"] = 4] = "Z3_SORT_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_FUNC_DECL_AST"] = 5] = "Z3_FUNC_DECL_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_UNKNOWN_AST"] = 1000] = "Z3_UNKNOWN_AST";
})(Z3_ast_kind = exports.Z3_ast_kind || (exports.Z3_ast_kind = {}));
var Z3_decl_kind;
(function (Z3_decl_kind) {
    Z3_decl_kind[Z3_decl_kind["Z3_OP_TRUE"] = 256] = "Z3_OP_TRUE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FALSE"] = 257] = "Z3_OP_FALSE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_EQ"] = 258] = "Z3_OP_EQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DISTINCT"] = 259] = "Z3_OP_DISTINCT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ITE"] = 260] = "Z3_OP_ITE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_AND"] = 261] = "Z3_OP_AND";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_OR"] = 262] = "Z3_OP_OR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_IFF"] = 263] = "Z3_OP_IFF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_XOR"] = 264] = "Z3_OP_XOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_NOT"] = 265] = "Z3_OP_NOT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_IMPLIES"] = 266] = "Z3_OP_IMPLIES";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_OEQ"] = 267] = "Z3_OP_OEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ANUM"] = 512] = "Z3_OP_ANUM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_AGNUM"] = 513] = "Z3_OP_AGNUM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_LE"] = 514] = "Z3_OP_LE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_GE"] = 515] = "Z3_OP_GE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_LT"] = 516] = "Z3_OP_LT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_GT"] = 517] = "Z3_OP_GT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ADD"] = 518] = "Z3_OP_ADD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SUB"] = 519] = "Z3_OP_SUB";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_UMINUS"] = 520] = "Z3_OP_UMINUS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_MUL"] = 521] = "Z3_OP_MUL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DIV"] = 522] = "Z3_OP_DIV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_IDIV"] = 523] = "Z3_OP_IDIV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_REM"] = 524] = "Z3_OP_REM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_MOD"] = 525] = "Z3_OP_MOD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_TO_REAL"] = 526] = "Z3_OP_TO_REAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_TO_INT"] = 527] = "Z3_OP_TO_INT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_IS_INT"] = 528] = "Z3_OP_IS_INT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_POWER"] = 529] = "Z3_OP_POWER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STORE"] = 768] = "Z3_OP_STORE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SELECT"] = 769] = "Z3_OP_SELECT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CONST_ARRAY"] = 770] = "Z3_OP_CONST_ARRAY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ARRAY_MAP"] = 771] = "Z3_OP_ARRAY_MAP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ARRAY_DEFAULT"] = 772] = "Z3_OP_ARRAY_DEFAULT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_UNION"] = 773] = "Z3_OP_SET_UNION";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_INTERSECT"] = 774] = "Z3_OP_SET_INTERSECT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_DIFFERENCE"] = 775] = "Z3_OP_SET_DIFFERENCE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_COMPLEMENT"] = 776] = "Z3_OP_SET_COMPLEMENT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_SUBSET"] = 777] = "Z3_OP_SET_SUBSET";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_AS_ARRAY"] = 778] = "Z3_OP_AS_ARRAY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ARRAY_EXT"] = 779] = "Z3_OP_ARRAY_EXT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_HAS_SIZE"] = 780] = "Z3_OP_SET_HAS_SIZE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_CARD"] = 781] = "Z3_OP_SET_CARD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BNUM"] = 1024] = "Z3_OP_BNUM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BIT1"] = 1025] = "Z3_OP_BIT1";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BIT0"] = 1026] = "Z3_OP_BIT0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BNEG"] = 1027] = "Z3_OP_BNEG";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BADD"] = 1028] = "Z3_OP_BADD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSUB"] = 1029] = "Z3_OP_BSUB";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BMUL"] = 1030] = "Z3_OP_BMUL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSDIV"] = 1031] = "Z3_OP_BSDIV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUDIV"] = 1032] = "Z3_OP_BUDIV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSREM"] = 1033] = "Z3_OP_BSREM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUREM"] = 1034] = "Z3_OP_BUREM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSMOD"] = 1035] = "Z3_OP_BSMOD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSDIV0"] = 1036] = "Z3_OP_BSDIV0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUDIV0"] = 1037] = "Z3_OP_BUDIV0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSREM0"] = 1038] = "Z3_OP_BSREM0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUREM0"] = 1039] = "Z3_OP_BUREM0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSMOD0"] = 1040] = "Z3_OP_BSMOD0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ULEQ"] = 1041] = "Z3_OP_ULEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SLEQ"] = 1042] = "Z3_OP_SLEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_UGEQ"] = 1043] = "Z3_OP_UGEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SGEQ"] = 1044] = "Z3_OP_SGEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ULT"] = 1045] = "Z3_OP_ULT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SLT"] = 1046] = "Z3_OP_SLT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_UGT"] = 1047] = "Z3_OP_UGT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SGT"] = 1048] = "Z3_OP_SGT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BAND"] = 1049] = "Z3_OP_BAND";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BOR"] = 1050] = "Z3_OP_BOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BNOT"] = 1051] = "Z3_OP_BNOT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BXOR"] = 1052] = "Z3_OP_BXOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BNAND"] = 1053] = "Z3_OP_BNAND";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BNOR"] = 1054] = "Z3_OP_BNOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BXNOR"] = 1055] = "Z3_OP_BXNOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CONCAT"] = 1056] = "Z3_OP_CONCAT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SIGN_EXT"] = 1057] = "Z3_OP_SIGN_EXT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ZERO_EXT"] = 1058] = "Z3_OP_ZERO_EXT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_EXTRACT"] = 1059] = "Z3_OP_EXTRACT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_REPEAT"] = 1060] = "Z3_OP_REPEAT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BREDOR"] = 1061] = "Z3_OP_BREDOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BREDAND"] = 1062] = "Z3_OP_BREDAND";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BCOMP"] = 1063] = "Z3_OP_BCOMP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSHL"] = 1064] = "Z3_OP_BSHL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BLSHR"] = 1065] = "Z3_OP_BLSHR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BASHR"] = 1066] = "Z3_OP_BASHR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ROTATE_LEFT"] = 1067] = "Z3_OP_ROTATE_LEFT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ROTATE_RIGHT"] = 1068] = "Z3_OP_ROTATE_RIGHT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_EXT_ROTATE_LEFT"] = 1069] = "Z3_OP_EXT_ROTATE_LEFT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_EXT_ROTATE_RIGHT"] = 1070] = "Z3_OP_EXT_ROTATE_RIGHT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BIT2BOOL"] = 1071] = "Z3_OP_BIT2BOOL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_INT2BV"] = 1072] = "Z3_OP_INT2BV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BV2INT"] = 1073] = "Z3_OP_BV2INT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CARRY"] = 1074] = "Z3_OP_CARRY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_XOR3"] = 1075] = "Z3_OP_XOR3";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSMUL_NO_OVFL"] = 1076] = "Z3_OP_BSMUL_NO_OVFL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUMUL_NO_OVFL"] = 1077] = "Z3_OP_BUMUL_NO_OVFL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSMUL_NO_UDFL"] = 1078] = "Z3_OP_BSMUL_NO_UDFL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSDIV_I"] = 1079] = "Z3_OP_BSDIV_I";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUDIV_I"] = 1080] = "Z3_OP_BUDIV_I";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSREM_I"] = 1081] = "Z3_OP_BSREM_I";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUREM_I"] = 1082] = "Z3_OP_BUREM_I";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSMOD_I"] = 1083] = "Z3_OP_BSMOD_I";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_UNDEF"] = 1280] = "Z3_OP_PR_UNDEF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_TRUE"] = 1281] = "Z3_OP_PR_TRUE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_ASSERTED"] = 1282] = "Z3_OP_PR_ASSERTED";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_GOAL"] = 1283] = "Z3_OP_PR_GOAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_MODUS_PONENS"] = 1284] = "Z3_OP_PR_MODUS_PONENS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_REFLEXIVITY"] = 1285] = "Z3_OP_PR_REFLEXIVITY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_SYMMETRY"] = 1286] = "Z3_OP_PR_SYMMETRY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_TRANSITIVITY"] = 1287] = "Z3_OP_PR_TRANSITIVITY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_TRANSITIVITY_STAR"] = 1288] = "Z3_OP_PR_TRANSITIVITY_STAR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_MONOTONICITY"] = 1289] = "Z3_OP_PR_MONOTONICITY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_QUANT_INTRO"] = 1290] = "Z3_OP_PR_QUANT_INTRO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_BIND"] = 1291] = "Z3_OP_PR_BIND";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_DISTRIBUTIVITY"] = 1292] = "Z3_OP_PR_DISTRIBUTIVITY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_AND_ELIM"] = 1293] = "Z3_OP_PR_AND_ELIM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_NOT_OR_ELIM"] = 1294] = "Z3_OP_PR_NOT_OR_ELIM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_REWRITE"] = 1295] = "Z3_OP_PR_REWRITE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_REWRITE_STAR"] = 1296] = "Z3_OP_PR_REWRITE_STAR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_PULL_QUANT"] = 1297] = "Z3_OP_PR_PULL_QUANT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_PUSH_QUANT"] = 1298] = "Z3_OP_PR_PUSH_QUANT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_ELIM_UNUSED_VARS"] = 1299] = "Z3_OP_PR_ELIM_UNUSED_VARS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_DER"] = 1300] = "Z3_OP_PR_DER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_QUANT_INST"] = 1301] = "Z3_OP_PR_QUANT_INST";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_HYPOTHESIS"] = 1302] = "Z3_OP_PR_HYPOTHESIS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_LEMMA"] = 1303] = "Z3_OP_PR_LEMMA";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_UNIT_RESOLUTION"] = 1304] = "Z3_OP_PR_UNIT_RESOLUTION";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_IFF_TRUE"] = 1305] = "Z3_OP_PR_IFF_TRUE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_IFF_FALSE"] = 1306] = "Z3_OP_PR_IFF_FALSE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_COMMUTATIVITY"] = 1307] = "Z3_OP_PR_COMMUTATIVITY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_DEF_AXIOM"] = 1308] = "Z3_OP_PR_DEF_AXIOM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_ASSUMPTION_ADD"] = 1309] = "Z3_OP_PR_ASSUMPTION_ADD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_LEMMA_ADD"] = 1310] = "Z3_OP_PR_LEMMA_ADD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_REDUNDANT_DEL"] = 1311] = "Z3_OP_PR_REDUNDANT_DEL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_CLAUSE_TRAIL"] = 1312] = "Z3_OP_PR_CLAUSE_TRAIL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_DEF_INTRO"] = 1313] = "Z3_OP_PR_DEF_INTRO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_APPLY_DEF"] = 1314] = "Z3_OP_PR_APPLY_DEF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_IFF_OEQ"] = 1315] = "Z3_OP_PR_IFF_OEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_NNF_POS"] = 1316] = "Z3_OP_PR_NNF_POS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_NNF_NEG"] = 1317] = "Z3_OP_PR_NNF_NEG";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_SKOLEMIZE"] = 1318] = "Z3_OP_PR_SKOLEMIZE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_MODUS_PONENS_OEQ"] = 1319] = "Z3_OP_PR_MODUS_PONENS_OEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_TH_LEMMA"] = 1320] = "Z3_OP_PR_TH_LEMMA";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_HYPER_RESOLVE"] = 1321] = "Z3_OP_PR_HYPER_RESOLVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_STORE"] = 1536] = "Z3_OP_RA_STORE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_EMPTY"] = 1537] = "Z3_OP_RA_EMPTY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_IS_EMPTY"] = 1538] = "Z3_OP_RA_IS_EMPTY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_JOIN"] = 1539] = "Z3_OP_RA_JOIN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_UNION"] = 1540] = "Z3_OP_RA_UNION";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_WIDEN"] = 1541] = "Z3_OP_RA_WIDEN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_PROJECT"] = 1542] = "Z3_OP_RA_PROJECT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_FILTER"] = 1543] = "Z3_OP_RA_FILTER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_NEGATION_FILTER"] = 1544] = "Z3_OP_RA_NEGATION_FILTER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_RENAME"] = 1545] = "Z3_OP_RA_RENAME";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_COMPLEMENT"] = 1546] = "Z3_OP_RA_COMPLEMENT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_SELECT"] = 1547] = "Z3_OP_RA_SELECT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_CLONE"] = 1548] = "Z3_OP_RA_CLONE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FD_CONSTANT"] = 1549] = "Z3_OP_FD_CONSTANT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FD_LT"] = 1550] = "Z3_OP_FD_LT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_UNIT"] = 1551] = "Z3_OP_SEQ_UNIT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_EMPTY"] = 1552] = "Z3_OP_SEQ_EMPTY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_CONCAT"] = 1553] = "Z3_OP_SEQ_CONCAT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_PREFIX"] = 1554] = "Z3_OP_SEQ_PREFIX";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_SUFFIX"] = 1555] = "Z3_OP_SEQ_SUFFIX";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_CONTAINS"] = 1556] = "Z3_OP_SEQ_CONTAINS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_EXTRACT"] = 1557] = "Z3_OP_SEQ_EXTRACT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_REPLACE"] = 1558] = "Z3_OP_SEQ_REPLACE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_REPLACE_RE"] = 1559] = "Z3_OP_SEQ_REPLACE_RE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_REPLACE_RE_ALL"] = 1560] = "Z3_OP_SEQ_REPLACE_RE_ALL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_REPLACE_ALL"] = 1561] = "Z3_OP_SEQ_REPLACE_ALL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_AT"] = 1562] = "Z3_OP_SEQ_AT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_NTH"] = 1563] = "Z3_OP_SEQ_NTH";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_LENGTH"] = 1564] = "Z3_OP_SEQ_LENGTH";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_INDEX"] = 1565] = "Z3_OP_SEQ_INDEX";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_LAST_INDEX"] = 1566] = "Z3_OP_SEQ_LAST_INDEX";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_TO_RE"] = 1567] = "Z3_OP_SEQ_TO_RE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_IN_RE"] = 1568] = "Z3_OP_SEQ_IN_RE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STR_TO_INT"] = 1569] = "Z3_OP_STR_TO_INT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_INT_TO_STR"] = 1570] = "Z3_OP_INT_TO_STR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_UBV_TO_STR"] = 1571] = "Z3_OP_UBV_TO_STR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SBV_TO_STR"] = 1572] = "Z3_OP_SBV_TO_STR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STR_TO_CODE"] = 1573] = "Z3_OP_STR_TO_CODE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STR_FROM_CODE"] = 1574] = "Z3_OP_STR_FROM_CODE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STRING_LT"] = 1575] = "Z3_OP_STRING_LT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STRING_LE"] = 1576] = "Z3_OP_STRING_LE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_PLUS"] = 1577] = "Z3_OP_RE_PLUS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_STAR"] = 1578] = "Z3_OP_RE_STAR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_OPTION"] = 1579] = "Z3_OP_RE_OPTION";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_CONCAT"] = 1580] = "Z3_OP_RE_CONCAT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_UNION"] = 1581] = "Z3_OP_RE_UNION";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_RANGE"] = 1582] = "Z3_OP_RE_RANGE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_DIFF"] = 1583] = "Z3_OP_RE_DIFF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_INTERSECT"] = 1584] = "Z3_OP_RE_INTERSECT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_LOOP"] = 1585] = "Z3_OP_RE_LOOP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_POWER"] = 1586] = "Z3_OP_RE_POWER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_COMPLEMENT"] = 1587] = "Z3_OP_RE_COMPLEMENT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_EMPTY_SET"] = 1588] = "Z3_OP_RE_EMPTY_SET";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_FULL_SET"] = 1589] = "Z3_OP_RE_FULL_SET";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_FULL_CHAR_SET"] = 1590] = "Z3_OP_RE_FULL_CHAR_SET";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_OF_PRED"] = 1591] = "Z3_OP_RE_OF_PRED";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_REVERSE"] = 1592] = "Z3_OP_RE_REVERSE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_DERIVATIVE"] = 1593] = "Z3_OP_RE_DERIVATIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_CONST"] = 1594] = "Z3_OP_CHAR_CONST";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_LE"] = 1595] = "Z3_OP_CHAR_LE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_TO_INT"] = 1596] = "Z3_OP_CHAR_TO_INT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_TO_BV"] = 1597] = "Z3_OP_CHAR_TO_BV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_FROM_BV"] = 1598] = "Z3_OP_CHAR_FROM_BV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_IS_DIGIT"] = 1599] = "Z3_OP_CHAR_IS_DIGIT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_LABEL"] = 1792] = "Z3_OP_LABEL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_LABEL_LIT"] = 1793] = "Z3_OP_LABEL_LIT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DT_CONSTRUCTOR"] = 2048] = "Z3_OP_DT_CONSTRUCTOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DT_RECOGNISER"] = 2049] = "Z3_OP_DT_RECOGNISER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DT_IS"] = 2050] = "Z3_OP_DT_IS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DT_ACCESSOR"] = 2051] = "Z3_OP_DT_ACCESSOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DT_UPDATE_FIELD"] = 2052] = "Z3_OP_DT_UPDATE_FIELD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PB_AT_MOST"] = 2304] = "Z3_OP_PB_AT_MOST";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PB_AT_LEAST"] = 2305] = "Z3_OP_PB_AT_LEAST";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PB_LE"] = 2306] = "Z3_OP_PB_LE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PB_GE"] = 2307] = "Z3_OP_PB_GE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PB_EQ"] = 2308] = "Z3_OP_PB_EQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_LO"] = 40960] = "Z3_OP_SPECIAL_RELATION_LO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_PO"] = 40961] = "Z3_OP_SPECIAL_RELATION_PO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_PLO"] = 40962] = "Z3_OP_SPECIAL_RELATION_PLO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_TO"] = 40963] = "Z3_OP_SPECIAL_RELATION_TO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_TC"] = 40964] = "Z3_OP_SPECIAL_RELATION_TC";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_TRC"] = 40965] = "Z3_OP_SPECIAL_RELATION_TRC";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN"] = 45056] = "Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY"] = 45057] = "Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_RM_TOWARD_POSITIVE"] = 45058] = "Z3_OP_FPA_RM_TOWARD_POSITIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_RM_TOWARD_NEGATIVE"] = 45059] = "Z3_OP_FPA_RM_TOWARD_NEGATIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_RM_TOWARD_ZERO"] = 45060] = "Z3_OP_FPA_RM_TOWARD_ZERO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_NUM"] = 45061] = "Z3_OP_FPA_NUM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_PLUS_INF"] = 45062] = "Z3_OP_FPA_PLUS_INF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_MINUS_INF"] = 45063] = "Z3_OP_FPA_MINUS_INF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_NAN"] = 45064] = "Z3_OP_FPA_NAN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_PLUS_ZERO"] = 45065] = "Z3_OP_FPA_PLUS_ZERO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_MINUS_ZERO"] = 45066] = "Z3_OP_FPA_MINUS_ZERO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_ADD"] = 45067] = "Z3_OP_FPA_ADD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_SUB"] = 45068] = "Z3_OP_FPA_SUB";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_NEG"] = 45069] = "Z3_OP_FPA_NEG";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_MUL"] = 45070] = "Z3_OP_FPA_MUL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_DIV"] = 45071] = "Z3_OP_FPA_DIV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_REM"] = 45072] = "Z3_OP_FPA_REM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_ABS"] = 45073] = "Z3_OP_FPA_ABS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_MIN"] = 45074] = "Z3_OP_FPA_MIN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_MAX"] = 45075] = "Z3_OP_FPA_MAX";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_FMA"] = 45076] = "Z3_OP_FPA_FMA";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_SQRT"] = 45077] = "Z3_OP_FPA_SQRT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_ROUND_TO_INTEGRAL"] = 45078] = "Z3_OP_FPA_ROUND_TO_INTEGRAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_EQ"] = 45079] = "Z3_OP_FPA_EQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_LT"] = 45080] = "Z3_OP_FPA_LT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_GT"] = 45081] = "Z3_OP_FPA_GT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_LE"] = 45082] = "Z3_OP_FPA_LE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_GE"] = 45083] = "Z3_OP_FPA_GE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_NAN"] = 45084] = "Z3_OP_FPA_IS_NAN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_INF"] = 45085] = "Z3_OP_FPA_IS_INF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_ZERO"] = 45086] = "Z3_OP_FPA_IS_ZERO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_NORMAL"] = 45087] = "Z3_OP_FPA_IS_NORMAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_SUBNORMAL"] = 45088] = "Z3_OP_FPA_IS_SUBNORMAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_NEGATIVE"] = 45089] = "Z3_OP_FPA_IS_NEGATIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_POSITIVE"] = 45090] = "Z3_OP_FPA_IS_POSITIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_FP"] = 45091] = "Z3_OP_FPA_FP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_FP"] = 45092] = "Z3_OP_FPA_TO_FP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_FP_UNSIGNED"] = 45093] = "Z3_OP_FPA_TO_FP_UNSIGNED";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_UBV"] = 45094] = "Z3_OP_FPA_TO_UBV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_SBV"] = 45095] = "Z3_OP_FPA_TO_SBV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_REAL"] = 45096] = "Z3_OP_FPA_TO_REAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_IEEE_BV"] = 45097] = "Z3_OP_FPA_TO_IEEE_BV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_BVWRAP"] = 45098] = "Z3_OP_FPA_BVWRAP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_BV2RM"] = 45099] = "Z3_OP_FPA_BV2RM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_INTERNAL"] = 45100] = "Z3_OP_INTERNAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RECURSIVE"] = 45101] = "Z3_OP_RECURSIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_UNINTERPRETED"] = 45102] = "Z3_OP_UNINTERPRETED";
})(Z3_decl_kind = exports.Z3_decl_kind || (exports.Z3_decl_kind = {}));
var Z3_param_kind;
(function (Z3_param_kind) {
    Z3_param_kind[Z3_param_kind["Z3_PK_UINT"] = 0] = "Z3_PK_UINT";
    Z3_param_kind[Z3_param_kind["Z3_PK_BOOL"] = 1] = "Z3_PK_BOOL";
    Z3_param_kind[Z3_param_kind["Z3_PK_DOUBLE"] = 2] = "Z3_PK_DOUBLE";
    Z3_param_kind[Z3_param_kind["Z3_PK_SYMBOL"] = 3] = "Z3_PK_SYMBOL";
    Z3_param_kind[Z3_param_kind["Z3_PK_STRING"] = 4] = "Z3_PK_STRING";
    Z3_param_kind[Z3_param_kind["Z3_PK_OTHER"] = 5] = "Z3_PK_OTHER";
    Z3_param_kind[Z3_param_kind["Z3_PK_INVALID"] = 6] = "Z3_PK_INVALID";
})(Z3_param_kind = exports.Z3_param_kind || (exports.Z3_param_kind = {}));
var Z3_ast_print_mode;
(function (Z3_ast_print_mode) {
    Z3_ast_print_mode[Z3_ast_print_mode["Z3_PRINT_SMTLIB_FULL"] = 0] = "Z3_PRINT_SMTLIB_FULL";
    Z3_ast_print_mode[Z3_ast_print_mode["Z3_PRINT_LOW_LEVEL"] = 1] = "Z3_PRINT_LOW_LEVEL";
    Z3_ast_print_mode[Z3_ast_print_mode["Z3_PRINT_SMTLIB2_COMPLIANT"] = 2] = "Z3_PRINT_SMTLIB2_COMPLIANT";
})(Z3_ast_print_mode = exports.Z3_ast_print_mode || (exports.Z3_ast_print_mode = {}));
var Z3_error_code;
(function (Z3_error_code) {
    Z3_error_code[Z3_error_code["Z3_OK"] = 0] = "Z3_OK";
    Z3_error_code[Z3_error_code["Z3_SORT_ERROR"] = 1] = "Z3_SORT_ERROR";
    Z3_error_code[Z3_error_code["Z3_IOB"] = 2] = "Z3_IOB";
    Z3_error_code[Z3_error_code["Z3_INVALID_ARG"] = 3] = "Z3_INVALID_ARG";
    Z3_error_code[Z3_error_code["Z3_PARSER_ERROR"] = 4] = "Z3_PARSER_ERROR";
    Z3_error_code[Z3_error_code["Z3_NO_PARSER"] = 5] = "Z3_NO_PARSER";
    Z3_error_code[Z3_error_code["Z3_INVALID_PATTERN"] = 6] = "Z3_INVALID_PATTERN";
    Z3_error_code[Z3_error_code["Z3_MEMOUT_FAIL"] = 7] = "Z3_MEMOUT_FAIL";
    Z3_error_code[Z3_error_code["Z3_FILE_ACCESS_ERROR"] = 8] = "Z3_FILE_ACCESS_ERROR";
    Z3_error_code[Z3_error_code["Z3_INTERNAL_FATAL"] = 9] = "Z3_INTERNAL_FATAL";
    Z3_error_code[Z3_error_code["Z3_INVALID_USAGE"] = 10] = "Z3_INVALID_USAGE";
    Z3_error_code[Z3_error_code["Z3_DEC_REF_ERROR"] = 11] = "Z3_DEC_REF_ERROR";
    Z3_error_code[Z3_error_code["Z3_EXCEPTION"] = 12] = "Z3_EXCEPTION";
})(Z3_error_code = exports.Z3_error_code || (exports.Z3_error_code = {}));
var Z3_goal_prec;
(function (Z3_goal_prec) {
    Z3_goal_prec[Z3_goal_prec["Z3_GOAL_PRECISE"] = 0] = "Z3_GOAL_PRECISE";
    Z3_goal_prec[Z3_goal_prec["Z3_GOAL_UNDER"] = 1] = "Z3_GOAL_UNDER";
    Z3_goal_prec[Z3_goal_prec["Z3_GOAL_OVER"] = 2] = "Z3_GOAL_OVER";
    Z3_goal_prec[Z3_goal_prec["Z3_GOAL_UNDER_OVER"] = 3] = "Z3_GOAL_UNDER_OVER";
})(Z3_goal_prec = exports.Z3_goal_prec || (exports.Z3_goal_prec = {}));

},{}],16:[function(require,module,exports){
"use strict";
// THIS FILE IS AUTOMATICALLY GENERATED BY make-ts-wrapper.ts
// DO NOT EDIT IT BY HAND
Object.defineProperty(exports, "__esModule", { value: true });
exports.init = void 0;
async function init(initModule) {
    let Mod = await initModule();
    // this works for both signed and unsigned, because JS will wrap for you when constructing the Uint32Array
    function intArrayToByteArr(ints) {
        return new Uint8Array(new Uint32Array(ints).buffer);
    }
    function boolArrayToByteArr(bools) {
        return bools.map((b) => (b ? 1 : 0));
    }
    function readUintArray(address, count) {
        return Array.from(new Uint32Array(Mod.HEAPU32.buffer, address, count));
    }
    let outAddress = Mod._malloc(24);
    let outUintArray = new Uint32Array(Mod.HEAPU32.buffer, outAddress, 4);
    let getOutUint = (i) => outUintArray[i];
    let outIntArray = new Int32Array(Mod.HEAPU32.buffer, outAddress, 4);
    let getOutInt = (i) => outIntArray[i];
    let outUint64Array = new BigUint64Array(Mod.HEAPU32.buffer, outAddress, 2);
    let getOutUint64 = (i) => outUint64Array[i];
    let outInt64Array = new BigInt64Array(Mod.HEAPU32.buffer, outAddress, 2);
    let getOutInt64 = (i) => outInt64Array[i];
    return {
        em: Mod,
        Z3: {
            mk_context: function (c) {
                let ctx = Mod._Z3_mk_context(c);
                Mod._set_noop_error_handler(ctx);
                return ctx;
            },
            mk_context_rc: function (c) {
                let ctx = Mod._Z3_mk_context_rc(c);
                Mod._set_noop_error_handler(ctx);
                return ctx;
            },
            global_param_set: function (param_id, param_value) {
                return Mod.ccall('Z3_global_param_set', 'void', ['string', 'string'], [param_id, param_value]);
            },
            global_param_reset_all: Mod._Z3_global_param_reset_all,
            global_param_get: function (param_id) {
                let ret = Mod.ccall('Z3_global_param_get', 'boolean', ['string', 'number'], [param_id, outAddress]);
                if (!ret) {
                    return null;
                }
                return Mod.UTF8ToString(getOutUint(0));
            },
            mk_config: Mod._Z3_mk_config,
            del_config: Mod._Z3_del_config,
            set_param_value: function (c, param_id, param_value) {
                return Mod.ccall('Z3_set_param_value', 'void', ['number', 'string', 'string'], [c, param_id, param_value]);
            },
            del_context: Mod._Z3_del_context,
            inc_ref: Mod._Z3_inc_ref,
            dec_ref: Mod._Z3_dec_ref,
            update_param_value: function (c, param_id, param_value) {
                return Mod.ccall('Z3_update_param_value', 'void', ['number', 'string', 'string'], [c, param_id, param_value]);
            },
            get_global_param_descrs: Mod._Z3_get_global_param_descrs,
            interrupt: Mod._Z3_interrupt,
            enable_concurrent_dec_ref: Mod._Z3_enable_concurrent_dec_ref,
            mk_params: Mod._Z3_mk_params,
            params_inc_ref: Mod._Z3_params_inc_ref,
            params_dec_ref: Mod._Z3_params_dec_ref,
            params_set_bool: Mod._Z3_params_set_bool,
            params_set_uint: Mod._Z3_params_set_uint,
            params_set_double: Mod._Z3_params_set_double,
            params_set_symbol: Mod._Z3_params_set_symbol,
            params_to_string: function (c, p) {
                return Mod.ccall('Z3_params_to_string', 'string', ['number', 'number'], [c, p]);
            },
            params_validate: Mod._Z3_params_validate,
            param_descrs_inc_ref: Mod._Z3_param_descrs_inc_ref,
            param_descrs_dec_ref: Mod._Z3_param_descrs_dec_ref,
            param_descrs_get_kind: Mod._Z3_param_descrs_get_kind,
            param_descrs_size: function (c, p) {
                let ret = Mod.ccall('Z3_param_descrs_size', 'number', ['number', 'number'], [c, p]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            param_descrs_get_name: Mod._Z3_param_descrs_get_name,
            param_descrs_get_documentation: function (c, p, s) {
                return Mod.ccall('Z3_param_descrs_get_documentation', 'string', ['number', 'number', 'number'], [c, p, s]);
            },
            param_descrs_to_string: function (c, p) {
                return Mod.ccall('Z3_param_descrs_to_string', 'string', ['number', 'number'], [c, p]);
            },
            mk_int_symbol: Mod._Z3_mk_int_symbol,
            mk_string_symbol: function (c, s) {
                return Mod.ccall('Z3_mk_string_symbol', 'number', ['number', 'string'], [c, s]);
            },
            mk_uninterpreted_sort: Mod._Z3_mk_uninterpreted_sort,
            mk_type_variable: Mod._Z3_mk_type_variable,
            mk_bool_sort: Mod._Z3_mk_bool_sort,
            mk_int_sort: Mod._Z3_mk_int_sort,
            mk_real_sort: Mod._Z3_mk_real_sort,
            mk_bv_sort: Mod._Z3_mk_bv_sort,
            mk_finite_domain_sort: Mod._Z3_mk_finite_domain_sort,
            mk_array_sort: Mod._Z3_mk_array_sort,
            mk_array_sort_n: function (c, domain, range) {
                return Mod.ccall('Z3_mk_array_sort_n', 'number', ['number', 'number', 'array', 'number'], [
                    c,
                    domain.length,
                    intArrayToByteArr(domain),
                    range,
                ]);
            },
            mk_tuple_sort: function (c, mk_tuple_name, field_names, field_sorts) {
                if (field_names.length !== field_sorts.length) {
                    throw new TypeError(`field_names and field_sorts must be the same length (got ${field_names.length} and {field_sorts.length})`);
                }
                let outArray_proj_decl = Mod._malloc(4 * field_names.length);
                try {
                    let ret = Mod.ccall('Z3_mk_tuple_sort', 'number', [
                        'number',
                        'number',
                        'number',
                        'array',
                        'array',
                        'number',
                        'number',
                    ], [
                        c,
                        mk_tuple_name,
                        field_names.length,
                        intArrayToByteArr(field_names),
                        intArrayToByteArr(field_sorts),
                        outAddress,
                        outArray_proj_decl,
                    ]);
                    return {
                        rv: ret,
                        mk_tuple_decl: getOutUint(0),
                        proj_decl: readUintArray(outArray_proj_decl, field_names.length),
                    };
                }
                finally {
                    Mod._free(outArray_proj_decl);
                }
            },
            mk_enumeration_sort: function (c, name, enum_names) {
                let outArray_enum_consts = Mod._malloc(4 * enum_names.length);
                try {
                    let outArray_enum_testers = Mod._malloc(4 * enum_names.length);
                    try {
                        let ret = Mod.ccall('Z3_mk_enumeration_sort', 'number', ['number', 'number', 'number', 'array', 'number', 'number'], [
                            c,
                            name,
                            enum_names.length,
                            intArrayToByteArr(enum_names),
                            outArray_enum_consts,
                            outArray_enum_testers,
                        ]);
                        return {
                            rv: ret,
                            enum_consts: readUintArray(outArray_enum_consts, enum_names.length),
                            enum_testers: readUintArray(outArray_enum_testers, enum_names.length),
                        };
                    }
                    finally {
                        Mod._free(outArray_enum_testers);
                    }
                }
                finally {
                    Mod._free(outArray_enum_consts);
                }
            },
            mk_list_sort: function (c, name, elem_sort) {
                let ret = Mod.ccall('Z3_mk_list_sort', 'number', [
                    'number',
                    'number',
                    'number',
                    'number',
                    'number',
                    'number',
                    'number',
                    'number',
                    'number',
                ], [
                    c,
                    name,
                    elem_sort,
                    outAddress,
                    outAddress + 4,
                    outAddress + 8,
                    outAddress + 12,
                    outAddress + 16,
                    outAddress + 20,
                ]);
                return {
                    rv: ret,
                    nil_decl: getOutUint(0),
                    is_nil_decl: getOutUint(1),
                    cons_decl: getOutUint(2),
                    is_cons_decl: getOutUint(3),
                    head_decl: getOutUint(4),
                    tail_decl: getOutUint(5),
                };
            },
            mk_constructor: function (c, name, recognizer, field_names, sorts, sort_refs) {
                if (field_names.length !== sorts.length) {
                    throw new TypeError(`field_names and sorts must be the same length (got ${field_names.length} and {sorts.length})`);
                }
                if (field_names.length !== sort_refs.length) {
                    throw new TypeError(`field_names and sort_refs must be the same length (got ${field_names.length} and {sort_refs.length})`);
                }
                return Mod.ccall('Z3_mk_constructor', 'number', ['number', 'number', 'number', 'number', 'array', 'array', 'array'], [
                    c,
                    name,
                    recognizer,
                    field_names.length,
                    intArrayToByteArr(field_names),
                    intArrayToByteArr(sorts),
                    intArrayToByteArr(sort_refs),
                ]);
            },
            constructor_num_fields: function (c, constr) {
                let ret = Mod.ccall('Z3_constructor_num_fields', 'number', ['number', 'number'], [c, constr]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            del_constructor: Mod._Z3_del_constructor,
            mk_datatype: function (c, name, constructors) {
                return Mod.ccall('Z3_mk_datatype', 'number', ['number', 'number', 'number', 'array'], [
                    c,
                    name,
                    constructors.length,
                    intArrayToByteArr(constructors),
                ]);
            },
            mk_datatype_sort: Mod._Z3_mk_datatype_sort,
            mk_constructor_list: function (c, constructors) {
                return Mod.ccall('Z3_mk_constructor_list', 'number', ['number', 'number', 'array'], [
                    c,
                    constructors.length,
                    intArrayToByteArr(constructors),
                ]);
            },
            del_constructor_list: Mod._Z3_del_constructor_list,
            mk_datatypes: function (c, sort_names, constructor_lists) {
                if (sort_names.length !== constructor_lists.length) {
                    throw new TypeError(`sort_names and constructor_lists must be the same length (got ${sort_names.length} and {constructor_lists.length})`);
                }
                let outArray_sorts = Mod._malloc(4 * sort_names.length);
                try {
                    let ret = Mod.ccall('Z3_mk_datatypes', 'void', ['number', 'number', 'array', 'number', 'array'], [
                        c,
                        sort_names.length,
                        intArrayToByteArr(sort_names),
                        outArray_sorts,
                        intArrayToByteArr(constructor_lists),
                    ]);
                    return readUintArray(outArray_sorts, sort_names.length);
                }
                finally {
                    Mod._free(outArray_sorts);
                }
            },
            query_constructor: function (c, constr, num_fields) {
                let outArray_accessors = Mod._malloc(4 * num_fields);
                try {
                    let ret = Mod.ccall('Z3_query_constructor', 'void', ['number', 'number', 'number', 'number', 'number', 'number'], [
                        c,
                        constr,
                        num_fields,
                        outAddress,
                        outAddress + 4,
                        outArray_accessors,
                    ]);
                    return {
                        constructor: getOutUint(0),
                        tester: getOutUint(1),
                        accessors: readUintArray(outArray_accessors, num_fields),
                    };
                }
                finally {
                    Mod._free(outArray_accessors);
                }
            },
            mk_func_decl: function (c, s, domain, range) {
                return Mod.ccall('Z3_mk_func_decl', 'number', ['number', 'number', 'number', 'array', 'number'], [
                    c,
                    s,
                    domain.length,
                    intArrayToByteArr(domain),
                    range,
                ]);
            },
            mk_app: function (c, d, args) {
                return Mod.ccall('Z3_mk_app', 'number', ['number', 'number', 'number', 'array'], [c, d, args.length, intArrayToByteArr(args)]);
            },
            mk_const: Mod._Z3_mk_const,
            mk_fresh_func_decl: function (c, prefix, domain, range) {
                return Mod.ccall('Z3_mk_fresh_func_decl', 'number', ['number', 'string', 'number', 'array', 'number'], [
                    c,
                    prefix,
                    domain.length,
                    intArrayToByteArr(domain),
                    range,
                ]);
            },
            mk_fresh_const: function (c, prefix, ty) {
                return Mod.ccall('Z3_mk_fresh_const', 'number', ['number', 'string', 'number'], [c, prefix, ty]);
            },
            mk_rec_func_decl: function (c, s, domain, range) {
                return Mod.ccall('Z3_mk_rec_func_decl', 'number', ['number', 'number', 'number', 'array', 'number'], [
                    c,
                    s,
                    domain.length,
                    intArrayToByteArr(domain),
                    range,
                ]);
            },
            add_rec_def: function (c, f, args, body) {
                return Mod.ccall('Z3_add_rec_def', 'void', ['number', 'number', 'number', 'array', 'number'], [
                    c,
                    f,
                    args.length,
                    intArrayToByteArr(args),
                    body,
                ]);
            },
            mk_true: Mod._Z3_mk_true,
            mk_false: Mod._Z3_mk_false,
            mk_eq: Mod._Z3_mk_eq,
            mk_distinct: function (c, args) {
                return Mod.ccall('Z3_mk_distinct', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_not: Mod._Z3_mk_not,
            mk_ite: Mod._Z3_mk_ite,
            mk_iff: Mod._Z3_mk_iff,
            mk_implies: Mod._Z3_mk_implies,
            mk_xor: Mod._Z3_mk_xor,
            mk_and: function (c, args) {
                return Mod.ccall('Z3_mk_and', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_or: function (c, args) {
                return Mod.ccall('Z3_mk_or', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_add: function (c, args) {
                return Mod.ccall('Z3_mk_add', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_mul: function (c, args) {
                return Mod.ccall('Z3_mk_mul', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_sub: function (c, args) {
                return Mod.ccall('Z3_mk_sub', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_unary_minus: Mod._Z3_mk_unary_minus,
            mk_div: Mod._Z3_mk_div,
            mk_mod: Mod._Z3_mk_mod,
            mk_rem: Mod._Z3_mk_rem,
            mk_power: Mod._Z3_mk_power,
            mk_lt: Mod._Z3_mk_lt,
            mk_le: Mod._Z3_mk_le,
            mk_gt: Mod._Z3_mk_gt,
            mk_ge: Mod._Z3_mk_ge,
            mk_divides: Mod._Z3_mk_divides,
            mk_int2real: Mod._Z3_mk_int2real,
            mk_real2int: Mod._Z3_mk_real2int,
            mk_is_int: Mod._Z3_mk_is_int,
            mk_bvnot: Mod._Z3_mk_bvnot,
            mk_bvredand: Mod._Z3_mk_bvredand,
            mk_bvredor: Mod._Z3_mk_bvredor,
            mk_bvand: Mod._Z3_mk_bvand,
            mk_bvor: Mod._Z3_mk_bvor,
            mk_bvxor: Mod._Z3_mk_bvxor,
            mk_bvnand: Mod._Z3_mk_bvnand,
            mk_bvnor: Mod._Z3_mk_bvnor,
            mk_bvxnor: Mod._Z3_mk_bvxnor,
            mk_bvneg: Mod._Z3_mk_bvneg,
            mk_bvadd: Mod._Z3_mk_bvadd,
            mk_bvsub: Mod._Z3_mk_bvsub,
            mk_bvmul: Mod._Z3_mk_bvmul,
            mk_bvudiv: Mod._Z3_mk_bvudiv,
            mk_bvsdiv: Mod._Z3_mk_bvsdiv,
            mk_bvurem: Mod._Z3_mk_bvurem,
            mk_bvsrem: Mod._Z3_mk_bvsrem,
            mk_bvsmod: Mod._Z3_mk_bvsmod,
            mk_bvult: Mod._Z3_mk_bvult,
            mk_bvslt: Mod._Z3_mk_bvslt,
            mk_bvule: Mod._Z3_mk_bvule,
            mk_bvsle: Mod._Z3_mk_bvsle,
            mk_bvuge: Mod._Z3_mk_bvuge,
            mk_bvsge: Mod._Z3_mk_bvsge,
            mk_bvugt: Mod._Z3_mk_bvugt,
            mk_bvsgt: Mod._Z3_mk_bvsgt,
            mk_concat: Mod._Z3_mk_concat,
            mk_extract: Mod._Z3_mk_extract,
            mk_sign_ext: Mod._Z3_mk_sign_ext,
            mk_zero_ext: Mod._Z3_mk_zero_ext,
            mk_repeat: Mod._Z3_mk_repeat,
            mk_bit2bool: Mod._Z3_mk_bit2bool,
            mk_bvshl: Mod._Z3_mk_bvshl,
            mk_bvlshr: Mod._Z3_mk_bvlshr,
            mk_bvashr: Mod._Z3_mk_bvashr,
            mk_rotate_left: Mod._Z3_mk_rotate_left,
            mk_rotate_right: Mod._Z3_mk_rotate_right,
            mk_ext_rotate_left: Mod._Z3_mk_ext_rotate_left,
            mk_ext_rotate_right: Mod._Z3_mk_ext_rotate_right,
            mk_int2bv: Mod._Z3_mk_int2bv,
            mk_bv2int: Mod._Z3_mk_bv2int,
            mk_bvadd_no_overflow: Mod._Z3_mk_bvadd_no_overflow,
            mk_bvadd_no_underflow: Mod._Z3_mk_bvadd_no_underflow,
            mk_bvsub_no_overflow: Mod._Z3_mk_bvsub_no_overflow,
            mk_bvsub_no_underflow: Mod._Z3_mk_bvsub_no_underflow,
            mk_bvsdiv_no_overflow: Mod._Z3_mk_bvsdiv_no_overflow,
            mk_bvneg_no_overflow: Mod._Z3_mk_bvneg_no_overflow,
            mk_bvmul_no_overflow: Mod._Z3_mk_bvmul_no_overflow,
            mk_bvmul_no_underflow: Mod._Z3_mk_bvmul_no_underflow,
            mk_select: Mod._Z3_mk_select,
            mk_select_n: function (c, a, idxs) {
                return Mod.ccall('Z3_mk_select_n', 'number', ['number', 'number', 'number', 'array'], [c, a, idxs.length, intArrayToByteArr(idxs)]);
            },
            mk_store: Mod._Z3_mk_store,
            mk_store_n: function (c, a, idxs, v) {
                return Mod.ccall('Z3_mk_store_n', 'number', ['number', 'number', 'number', 'array', 'number'], [c, a, idxs.length, intArrayToByteArr(idxs), v]);
            },
            mk_const_array: Mod._Z3_mk_const_array,
            mk_map: function (c, f, args) {
                return Mod.ccall('Z3_mk_map', 'number', ['number', 'number', 'number', 'array'], [c, f, args.length, intArrayToByteArr(args)]);
            },
            mk_array_default: Mod._Z3_mk_array_default,
            mk_as_array: Mod._Z3_mk_as_array,
            mk_set_has_size: Mod._Z3_mk_set_has_size,
            mk_set_sort: Mod._Z3_mk_set_sort,
            mk_empty_set: Mod._Z3_mk_empty_set,
            mk_full_set: Mod._Z3_mk_full_set,
            mk_set_add: Mod._Z3_mk_set_add,
            mk_set_del: Mod._Z3_mk_set_del,
            mk_set_union: function (c, args) {
                return Mod.ccall('Z3_mk_set_union', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_set_intersect: function (c, args) {
                return Mod.ccall('Z3_mk_set_intersect', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_set_difference: Mod._Z3_mk_set_difference,
            mk_set_complement: Mod._Z3_mk_set_complement,
            mk_set_member: Mod._Z3_mk_set_member,
            mk_set_subset: Mod._Z3_mk_set_subset,
            mk_array_ext: Mod._Z3_mk_array_ext,
            mk_numeral: function (c, numeral, ty) {
                return Mod.ccall('Z3_mk_numeral', 'number', ['number', 'string', 'number'], [c, numeral, ty]);
            },
            mk_real: Mod._Z3_mk_real,
            mk_real_int64: Mod._Z3_mk_real_int64,
            mk_int: Mod._Z3_mk_int,
            mk_unsigned_int: Mod._Z3_mk_unsigned_int,
            mk_int64: Mod._Z3_mk_int64,
            mk_unsigned_int64: Mod._Z3_mk_unsigned_int64,
            mk_bv_numeral: function (c, bits) {
                return Mod.ccall('Z3_mk_bv_numeral', 'number', ['number', 'number', 'array'], [c, bits.length, boolArrayToByteArr(bits)]);
            },
            mk_seq_sort: Mod._Z3_mk_seq_sort,
            is_seq_sort: function (c, s) {
                return Mod.ccall('Z3_is_seq_sort', 'boolean', ['number', 'number'], [c, s]);
            },
            get_seq_sort_basis: Mod._Z3_get_seq_sort_basis,
            mk_re_sort: Mod._Z3_mk_re_sort,
            is_re_sort: function (c, s) {
                return Mod.ccall('Z3_is_re_sort', 'boolean', ['number', 'number'], [c, s]);
            },
            get_re_sort_basis: Mod._Z3_get_re_sort_basis,
            mk_string_sort: Mod._Z3_mk_string_sort,
            mk_char_sort: Mod._Z3_mk_char_sort,
            is_string_sort: function (c, s) {
                return Mod.ccall('Z3_is_string_sort', 'boolean', ['number', 'number'], [c, s]);
            },
            is_char_sort: function (c, s) {
                return Mod.ccall('Z3_is_char_sort', 'boolean', ['number', 'number'], [c, s]);
            },
            mk_string: function (c, s) {
                return Mod.ccall('Z3_mk_string', 'number', ['number', 'string'], [c, s]);
            },
            mk_lstring: function (c, len, s) {
                return Mod.ccall('Z3_mk_lstring', 'number', ['number', 'number', 'string'], [c, len, s]);
            },
            mk_u32string: function (c, chars) {
                return Mod.ccall('Z3_mk_u32string', 'number', ['number', 'number', 'array'], [c, chars.length, intArrayToByteArr(chars)]);
            },
            is_string: function (c, s) {
                return Mod.ccall('Z3_is_string', 'boolean', ['number', 'number'], [c, s]);
            },
            get_string: function (c, s) {
                return Mod.ccall('Z3_get_string', 'string', ['number', 'number'], [c, s]);
            },
            get_string_length: function (c, s) {
                let ret = Mod.ccall('Z3_get_string_length', 'number', ['number', 'number'], [c, s]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_string_contents: function (c, s, length) {
                let outArray_contents = Mod._malloc(4 * length);
                try {
                    let ret = Mod.ccall('Z3_get_string_contents', 'void', ['number', 'number', 'number', 'number'], [c, s, length, outArray_contents]);
                    return readUintArray(outArray_contents, length);
                }
                finally {
                    Mod._free(outArray_contents);
                }
            },
            mk_seq_empty: Mod._Z3_mk_seq_empty,
            mk_seq_unit: Mod._Z3_mk_seq_unit,
            mk_seq_concat: function (c, args) {
                return Mod.ccall('Z3_mk_seq_concat', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_seq_prefix: Mod._Z3_mk_seq_prefix,
            mk_seq_suffix: Mod._Z3_mk_seq_suffix,
            mk_seq_contains: Mod._Z3_mk_seq_contains,
            mk_str_lt: Mod._Z3_mk_str_lt,
            mk_str_le: Mod._Z3_mk_str_le,
            mk_seq_extract: Mod._Z3_mk_seq_extract,
            mk_seq_replace: Mod._Z3_mk_seq_replace,
            mk_seq_at: Mod._Z3_mk_seq_at,
            mk_seq_nth: Mod._Z3_mk_seq_nth,
            mk_seq_length: Mod._Z3_mk_seq_length,
            mk_seq_index: Mod._Z3_mk_seq_index,
            mk_seq_last_index: Mod._Z3_mk_seq_last_index,
            mk_str_to_int: Mod._Z3_mk_str_to_int,
            mk_int_to_str: Mod._Z3_mk_int_to_str,
            mk_string_to_code: Mod._Z3_mk_string_to_code,
            mk_string_from_code: Mod._Z3_mk_string_from_code,
            mk_ubv_to_str: Mod._Z3_mk_ubv_to_str,
            mk_sbv_to_str: Mod._Z3_mk_sbv_to_str,
            mk_seq_to_re: Mod._Z3_mk_seq_to_re,
            mk_seq_in_re: Mod._Z3_mk_seq_in_re,
            mk_re_plus: Mod._Z3_mk_re_plus,
            mk_re_star: Mod._Z3_mk_re_star,
            mk_re_option: Mod._Z3_mk_re_option,
            mk_re_union: function (c, args) {
                return Mod.ccall('Z3_mk_re_union', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_re_concat: function (c, args) {
                return Mod.ccall('Z3_mk_re_concat', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_re_range: Mod._Z3_mk_re_range,
            mk_re_allchar: Mod._Z3_mk_re_allchar,
            mk_re_loop: Mod._Z3_mk_re_loop,
            mk_re_power: Mod._Z3_mk_re_power,
            mk_re_intersect: function (c, args) {
                return Mod.ccall('Z3_mk_re_intersect', 'number', ['number', 'number', 'array'], [c, args.length, intArrayToByteArr(args)]);
            },
            mk_re_complement: Mod._Z3_mk_re_complement,
            mk_re_diff: Mod._Z3_mk_re_diff,
            mk_re_empty: Mod._Z3_mk_re_empty,
            mk_re_full: Mod._Z3_mk_re_full,
            mk_char: Mod._Z3_mk_char,
            mk_char_le: Mod._Z3_mk_char_le,
            mk_char_to_int: Mod._Z3_mk_char_to_int,
            mk_char_to_bv: Mod._Z3_mk_char_to_bv,
            mk_char_from_bv: Mod._Z3_mk_char_from_bv,
            mk_char_is_digit: Mod._Z3_mk_char_is_digit,
            mk_linear_order: Mod._Z3_mk_linear_order,
            mk_partial_order: Mod._Z3_mk_partial_order,
            mk_piecewise_linear_order: Mod._Z3_mk_piecewise_linear_order,
            mk_tree_order: Mod._Z3_mk_tree_order,
            mk_transitive_closure: Mod._Z3_mk_transitive_closure,
            mk_pattern: function (c, terms) {
                return Mod.ccall('Z3_mk_pattern', 'number', ['number', 'number', 'array'], [c, terms.length, intArrayToByteArr(terms)]);
            },
            mk_bound: Mod._Z3_mk_bound,
            mk_forall: function (c, weight, patterns, sorts, decl_names, body) {
                if (sorts.length !== decl_names.length) {
                    throw new TypeError(`sorts and decl_names must be the same length (got ${sorts.length} and {decl_names.length})`);
                }
                return Mod.ccall('Z3_mk_forall', 'number', [
                    'number',
                    'number',
                    'number',
                    'array',
                    'number',
                    'array',
                    'array',
                    'number',
                ], [
                    c,
                    weight,
                    patterns.length,
                    intArrayToByteArr(patterns),
                    sorts.length,
                    intArrayToByteArr(sorts),
                    intArrayToByteArr(decl_names),
                    body,
                ]);
            },
            mk_exists: function (c, weight, patterns, sorts, decl_names, body) {
                if (sorts.length !== decl_names.length) {
                    throw new TypeError(`sorts and decl_names must be the same length (got ${sorts.length} and {decl_names.length})`);
                }
                return Mod.ccall('Z3_mk_exists', 'number', [
                    'number',
                    'number',
                    'number',
                    'array',
                    'number',
                    'array',
                    'array',
                    'number',
                ], [
                    c,
                    weight,
                    patterns.length,
                    intArrayToByteArr(patterns),
                    sorts.length,
                    intArrayToByteArr(sorts),
                    intArrayToByteArr(decl_names),
                    body,
                ]);
            },
            mk_quantifier: function (c, is_forall, weight, patterns, sorts, decl_names, body) {
                if (sorts.length !== decl_names.length) {
                    throw new TypeError(`sorts and decl_names must be the same length (got ${sorts.length} and {decl_names.length})`);
                }
                return Mod.ccall('Z3_mk_quantifier', 'number', [
                    'number',
                    'boolean',
                    'number',
                    'number',
                    'array',
                    'number',
                    'array',
                    'array',
                    'number',
                ], [
                    c,
                    is_forall,
                    weight,
                    patterns.length,
                    intArrayToByteArr(patterns),
                    sorts.length,
                    intArrayToByteArr(sorts),
                    intArrayToByteArr(decl_names),
                    body,
                ]);
            },
            mk_quantifier_ex: function (c, is_forall, weight, quantifier_id, skolem_id, patterns, no_patterns, sorts, decl_names, body) {
                if (sorts.length !== decl_names.length) {
                    throw new TypeError(`sorts and decl_names must be the same length (got ${sorts.length} and {decl_names.length})`);
                }
                return Mod.ccall('Z3_mk_quantifier_ex', 'number', [
                    'number',
                    'boolean',
                    'number',
                    'number',
                    'number',
                    'number',
                    'array',
                    'number',
                    'array',
                    'number',
                    'array',
                    'array',
                    'number',
                ], [
                    c,
                    is_forall,
                    weight,
                    quantifier_id,
                    skolem_id,
                    patterns.length,
                    intArrayToByteArr(patterns),
                    no_patterns.length,
                    intArrayToByteArr(no_patterns),
                    sorts.length,
                    intArrayToByteArr(sorts),
                    intArrayToByteArr(decl_names),
                    body,
                ]);
            },
            mk_forall_const: function (c, weight, bound, patterns, body) {
                return Mod.ccall('Z3_mk_forall_const', 'number', ['number', 'number', 'number', 'array', 'number', 'array', 'number'], [
                    c,
                    weight,
                    bound.length,
                    intArrayToByteArr(bound),
                    patterns.length,
                    intArrayToByteArr(patterns),
                    body,
                ]);
            },
            mk_exists_const: function (c, weight, bound, patterns, body) {
                return Mod.ccall('Z3_mk_exists_const', 'number', ['number', 'number', 'number', 'array', 'number', 'array', 'number'], [
                    c,
                    weight,
                    bound.length,
                    intArrayToByteArr(bound),
                    patterns.length,
                    intArrayToByteArr(patterns),
                    body,
                ]);
            },
            mk_quantifier_const: function (c, is_forall, weight, bound, patterns, body) {
                return Mod.ccall('Z3_mk_quantifier_const', 'number', [
                    'number',
                    'boolean',
                    'number',
                    'number',
                    'array',
                    'number',
                    'array',
                    'number',
                ], [
                    c,
                    is_forall,
                    weight,
                    bound.length,
                    intArrayToByteArr(bound),
                    patterns.length,
                    intArrayToByteArr(patterns),
                    body,
                ]);
            },
            mk_quantifier_const_ex: function (c, is_forall, weight, quantifier_id, skolem_id, bound, patterns, no_patterns, body) {
                return Mod.ccall('Z3_mk_quantifier_const_ex', 'number', [
                    'number',
                    'boolean',
                    'number',
                    'number',
                    'number',
                    'number',
                    'array',
                    'number',
                    'array',
                    'number',
                    'array',
                    'number',
                ], [
                    c,
                    is_forall,
                    weight,
                    quantifier_id,
                    skolem_id,
                    bound.length,
                    intArrayToByteArr(bound),
                    patterns.length,
                    intArrayToByteArr(patterns),
                    no_patterns.length,
                    intArrayToByteArr(no_patterns),
                    body,
                ]);
            },
            mk_lambda: function (c, sorts, decl_names, body) {
                if (sorts.length !== decl_names.length) {
                    throw new TypeError(`sorts and decl_names must be the same length (got ${sorts.length} and {decl_names.length})`);
                }
                return Mod.ccall('Z3_mk_lambda', 'number', ['number', 'number', 'array', 'array', 'number'], [
                    c,
                    sorts.length,
                    intArrayToByteArr(sorts),
                    intArrayToByteArr(decl_names),
                    body,
                ]);
            },
            mk_lambda_const: function (c, bound, body) {
                return Mod.ccall('Z3_mk_lambda_const', 'number', ['number', 'number', 'array', 'number'], [
                    c,
                    bound.length,
                    intArrayToByteArr(bound),
                    body,
                ]);
            },
            get_symbol_kind: Mod._Z3_get_symbol_kind,
            get_symbol_int: Mod._Z3_get_symbol_int,
            get_symbol_string: function (c, s) {
                return Mod.ccall('Z3_get_symbol_string', 'string', ['number', 'number'], [c, s]);
            },
            get_sort_name: Mod._Z3_get_sort_name,
            get_sort_id: function (c, s) {
                let ret = Mod.ccall('Z3_get_sort_id', 'number', ['number', 'number'], [c, s]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            sort_to_ast: Mod._Z3_sort_to_ast,
            is_eq_sort: function (c, s1, s2) {
                return Mod.ccall('Z3_is_eq_sort', 'boolean', ['number', 'number', 'number'], [c, s1, s2]);
            },
            get_sort_kind: Mod._Z3_get_sort_kind,
            get_bv_sort_size: function (c, t) {
                let ret = Mod.ccall('Z3_get_bv_sort_size', 'number', ['number', 'number'], [c, t]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_finite_domain_sort_size: function (c, s) {
                let ret = Mod.ccall('Z3_get_finite_domain_sort_size', 'boolean', ['number', 'number', 'number'], [c, s, outAddress]);
                if (!ret) {
                    return null;
                }
                return getOutUint64(0);
            },
            get_array_sort_domain: Mod._Z3_get_array_sort_domain,
            get_array_sort_domain_n: Mod._Z3_get_array_sort_domain_n,
            get_array_sort_range: Mod._Z3_get_array_sort_range,
            get_tuple_sort_mk_decl: Mod._Z3_get_tuple_sort_mk_decl,
            get_tuple_sort_num_fields: function (c, t) {
                let ret = Mod.ccall('Z3_get_tuple_sort_num_fields', 'number', ['number', 'number'], [c, t]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_tuple_sort_field_decl: Mod._Z3_get_tuple_sort_field_decl,
            get_datatype_sort_num_constructors: function (c, t) {
                let ret = Mod.ccall('Z3_get_datatype_sort_num_constructors', 'number', ['number', 'number'], [c, t]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_datatype_sort_constructor: Mod._Z3_get_datatype_sort_constructor,
            get_datatype_sort_recognizer: Mod._Z3_get_datatype_sort_recognizer,
            get_datatype_sort_constructor_accessor: Mod._Z3_get_datatype_sort_constructor_accessor,
            datatype_update_field: Mod._Z3_datatype_update_field,
            get_relation_arity: function (c, s) {
                let ret = Mod.ccall('Z3_get_relation_arity', 'number', ['number', 'number'], [c, s]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_relation_column: Mod._Z3_get_relation_column,
            mk_atmost: function (c, args, k) {
                return Mod.ccall('Z3_mk_atmost', 'number', ['number', 'number', 'array', 'number'], [c, args.length, intArrayToByteArr(args), k]);
            },
            mk_atleast: function (c, args, k) {
                return Mod.ccall('Z3_mk_atleast', 'number', ['number', 'number', 'array', 'number'], [c, args.length, intArrayToByteArr(args), k]);
            },
            mk_pble: function (c, args, coeffs, k) {
                if (args.length !== coeffs.length) {
                    throw new TypeError(`args and coeffs must be the same length (got ${args.length} and {coeffs.length})`);
                }
                return Mod.ccall('Z3_mk_pble', 'number', ['number', 'number', 'array', 'array', 'number'], [
                    c,
                    args.length,
                    intArrayToByteArr(args),
                    intArrayToByteArr(coeffs),
                    k,
                ]);
            },
            mk_pbge: function (c, args, coeffs, k) {
                if (args.length !== coeffs.length) {
                    throw new TypeError(`args and coeffs must be the same length (got ${args.length} and {coeffs.length})`);
                }
                return Mod.ccall('Z3_mk_pbge', 'number', ['number', 'number', 'array', 'array', 'number'], [
                    c,
                    args.length,
                    intArrayToByteArr(args),
                    intArrayToByteArr(coeffs),
                    k,
                ]);
            },
            mk_pbeq: function (c, args, coeffs, k) {
                if (args.length !== coeffs.length) {
                    throw new TypeError(`args and coeffs must be the same length (got ${args.length} and {coeffs.length})`);
                }
                return Mod.ccall('Z3_mk_pbeq', 'number', ['number', 'number', 'array', 'array', 'number'], [
                    c,
                    args.length,
                    intArrayToByteArr(args),
                    intArrayToByteArr(coeffs),
                    k,
                ]);
            },
            func_decl_to_ast: Mod._Z3_func_decl_to_ast,
            is_eq_func_decl: function (c, f1, f2) {
                return Mod.ccall('Z3_is_eq_func_decl', 'boolean', ['number', 'number', 'number'], [c, f1, f2]);
            },
            get_func_decl_id: function (c, f) {
                let ret = Mod.ccall('Z3_get_func_decl_id', 'number', ['number', 'number'], [c, f]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_decl_name: Mod._Z3_get_decl_name,
            get_decl_kind: Mod._Z3_get_decl_kind,
            get_domain_size: function (c, d) {
                let ret = Mod.ccall('Z3_get_domain_size', 'number', ['number', 'number'], [c, d]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_arity: function (c, d) {
                let ret = Mod.ccall('Z3_get_arity', 'number', ['number', 'number'], [c, d]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_domain: Mod._Z3_get_domain,
            get_range: Mod._Z3_get_range,
            get_decl_num_parameters: function (c, d) {
                let ret = Mod.ccall('Z3_get_decl_num_parameters', 'number', ['number', 'number'], [c, d]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_decl_parameter_kind: Mod._Z3_get_decl_parameter_kind,
            get_decl_int_parameter: Mod._Z3_get_decl_int_parameter,
            get_decl_double_parameter: Mod._Z3_get_decl_double_parameter,
            get_decl_symbol_parameter: Mod._Z3_get_decl_symbol_parameter,
            get_decl_sort_parameter: Mod._Z3_get_decl_sort_parameter,
            get_decl_ast_parameter: Mod._Z3_get_decl_ast_parameter,
            get_decl_func_decl_parameter: Mod._Z3_get_decl_func_decl_parameter,
            get_decl_rational_parameter: function (c, d, idx) {
                return Mod.ccall('Z3_get_decl_rational_parameter', 'string', ['number', 'number', 'number'], [c, d, idx]);
            },
            app_to_ast: Mod._Z3_app_to_ast,
            get_app_decl: Mod._Z3_get_app_decl,
            get_app_num_args: function (c, a) {
                let ret = Mod.ccall('Z3_get_app_num_args', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_app_arg: Mod._Z3_get_app_arg,
            is_eq_ast: function (c, t1, t2) {
                return Mod.ccall('Z3_is_eq_ast', 'boolean', ['number', 'number', 'number'], [c, t1, t2]);
            },
            get_ast_id: function (c, t) {
                let ret = Mod.ccall('Z3_get_ast_id', 'number', ['number', 'number'], [c, t]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_ast_hash: function (c, a) {
                let ret = Mod.ccall('Z3_get_ast_hash', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_sort: Mod._Z3_get_sort,
            is_well_sorted: function (c, t) {
                return Mod.ccall('Z3_is_well_sorted', 'boolean', ['number', 'number'], [c, t]);
            },
            get_bool_value: Mod._Z3_get_bool_value,
            get_ast_kind: Mod._Z3_get_ast_kind,
            is_app: function (c, a) {
                return Mod.ccall('Z3_is_app', 'boolean', ['number', 'number'], [c, a]);
            },
            is_numeral_ast: function (c, a) {
                return Mod.ccall('Z3_is_numeral_ast', 'boolean', ['number', 'number'], [c, a]);
            },
            is_algebraic_number: function (c, a) {
                return Mod.ccall('Z3_is_algebraic_number', 'boolean', ['number', 'number'], [c, a]);
            },
            to_app: Mod._Z3_to_app,
            to_func_decl: Mod._Z3_to_func_decl,
            get_numeral_string: function (c, a) {
                return Mod.ccall('Z3_get_numeral_string', 'string', ['number', 'number'], [c, a]);
            },
            get_numeral_binary_string: function (c, a) {
                return Mod.ccall('Z3_get_numeral_binary_string', 'string', ['number', 'number'], [c, a]);
            },
            get_numeral_decimal_string: function (c, a, precision) {
                return Mod.ccall('Z3_get_numeral_decimal_string', 'string', ['number', 'number', 'number'], [c, a, precision]);
            },
            get_numeral_double: Mod._Z3_get_numeral_double,
            get_numerator: Mod._Z3_get_numerator,
            get_denominator: Mod._Z3_get_denominator,
            get_numeral_small: function (c, a) {
                let ret = Mod.ccall('Z3_get_numeral_small', 'boolean', ['number', 'number', 'number', 'number'], [c, a, outAddress, outAddress + 8]);
                if (!ret) {
                    return null;
                }
                return { num: getOutInt64(0), den: getOutInt64(1) };
            },
            get_numeral_int: function (c, v) {
                let ret = Mod.ccall('Z3_get_numeral_int', 'boolean', ['number', 'number', 'number'], [c, v, outAddress]);
                if (!ret) {
                    return null;
                }
                return getOutInt(0);
            },
            get_numeral_uint: function (c, v) {
                let ret = Mod.ccall('Z3_get_numeral_uint', 'boolean', ['number', 'number', 'number'], [c, v, outAddress]);
                if (!ret) {
                    return null;
                }
                return getOutUint(0);
            },
            get_numeral_uint64: function (c, v) {
                let ret = Mod.ccall('Z3_get_numeral_uint64', 'boolean', ['number', 'number', 'number'], [c, v, outAddress]);
                if (!ret) {
                    return null;
                }
                return getOutUint64(0);
            },
            get_numeral_int64: function (c, v) {
                let ret = Mod.ccall('Z3_get_numeral_int64', 'boolean', ['number', 'number', 'number'], [c, v, outAddress]);
                if (!ret) {
                    return null;
                }
                return getOutInt64(0);
            },
            get_numeral_rational_int64: function (c, v) {
                let ret = Mod.ccall('Z3_get_numeral_rational_int64', 'boolean', ['number', 'number', 'number', 'number'], [c, v, outAddress, outAddress + 8]);
                if (!ret) {
                    return null;
                }
                return { num: getOutInt64(0), den: getOutInt64(1) };
            },
            get_algebraic_number_lower: Mod._Z3_get_algebraic_number_lower,
            get_algebraic_number_upper: Mod._Z3_get_algebraic_number_upper,
            pattern_to_ast: Mod._Z3_pattern_to_ast,
            get_pattern_num_terms: function (c, p) {
                let ret = Mod.ccall('Z3_get_pattern_num_terms', 'number', ['number', 'number'], [c, p]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_pattern: Mod._Z3_get_pattern,
            get_index_value: function (c, a) {
                let ret = Mod.ccall('Z3_get_index_value', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            is_quantifier_forall: function (c, a) {
                return Mod.ccall('Z3_is_quantifier_forall', 'boolean', ['number', 'number'], [c, a]);
            },
            is_quantifier_exists: function (c, a) {
                return Mod.ccall('Z3_is_quantifier_exists', 'boolean', ['number', 'number'], [c, a]);
            },
            is_lambda: function (c, a) {
                return Mod.ccall('Z3_is_lambda', 'boolean', ['number', 'number'], [c, a]);
            },
            get_quantifier_weight: function (c, a) {
                let ret = Mod.ccall('Z3_get_quantifier_weight', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_quantifier_skolem_id: Mod._Z3_get_quantifier_skolem_id,
            get_quantifier_id: Mod._Z3_get_quantifier_id,
            get_quantifier_num_patterns: function (c, a) {
                let ret = Mod.ccall('Z3_get_quantifier_num_patterns', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_quantifier_pattern_ast: Mod._Z3_get_quantifier_pattern_ast,
            get_quantifier_num_no_patterns: function (c, a) {
                let ret = Mod.ccall('Z3_get_quantifier_num_no_patterns', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_quantifier_no_pattern_ast: Mod._Z3_get_quantifier_no_pattern_ast,
            get_quantifier_num_bound: function (c, a) {
                let ret = Mod.ccall('Z3_get_quantifier_num_bound', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_quantifier_bound_name: Mod._Z3_get_quantifier_bound_name,
            get_quantifier_bound_sort: Mod._Z3_get_quantifier_bound_sort,
            get_quantifier_body: Mod._Z3_get_quantifier_body,
            simplify: function (c, a) {
                return Mod.async_call(Mod._async_Z3_simplify, c, a);
            },
            simplify_ex: function (c, a, p) {
                return Mod.async_call(Mod._async_Z3_simplify_ex, c, a, p);
            },
            simplify_get_help: function (c) {
                return Mod.ccall('Z3_simplify_get_help', 'string', ['number'], [c]);
            },
            simplify_get_param_descrs: Mod._Z3_simplify_get_param_descrs,
            update_term: function (c, a, args) {
                return Mod.ccall('Z3_update_term', 'number', ['number', 'number', 'number', 'array'], [c, a, args.length, intArrayToByteArr(args)]);
            },
            substitute: function (c, a, from, to) {
                if (from.length !== to.length) {
                    throw new TypeError(`from and to must be the same length (got ${from.length} and {to.length})`);
                }
                return Mod.ccall('Z3_substitute', 'number', ['number', 'number', 'number', 'array', 'array'], [
                    c,
                    a,
                    from.length,
                    intArrayToByteArr(from),
                    intArrayToByteArr(to),
                ]);
            },
            substitute_vars: function (c, a, to) {
                return Mod.ccall('Z3_substitute_vars', 'number', ['number', 'number', 'number', 'array'], [c, a, to.length, intArrayToByteArr(to)]);
            },
            substitute_funs: function (c, a, from, to) {
                if (from.length !== to.length) {
                    throw new TypeError(`from and to must be the same length (got ${from.length} and {to.length})`);
                }
                return Mod.ccall('Z3_substitute_funs', 'number', ['number', 'number', 'number', 'array', 'array'], [
                    c,
                    a,
                    from.length,
                    intArrayToByteArr(from),
                    intArrayToByteArr(to),
                ]);
            },
            translate: Mod._Z3_translate,
            mk_model: Mod._Z3_mk_model,
            model_inc_ref: Mod._Z3_model_inc_ref,
            model_dec_ref: Mod._Z3_model_dec_ref,
            model_eval: function (c, m, t, model_completion) {
                let ret = Mod.ccall('Z3_model_eval', 'boolean', ['number', 'number', 'number', 'boolean', 'number'], [c, m, t, model_completion, outAddress]);
                if (!ret) {
                    return null;
                }
                return getOutUint(0);
            },
            model_get_const_interp: function (c, m, a) {
                let ret = Mod.ccall('Z3_model_get_const_interp', 'number', ['number', 'number', 'number'], [c, m, a]);
                if (ret === 0) {
                    return null;
                }
                return ret;
            },
            model_has_interp: function (c, m, a) {
                return Mod.ccall('Z3_model_has_interp', 'boolean', ['number', 'number', 'number'], [c, m, a]);
            },
            model_get_func_interp: function (c, m, f) {
                let ret = Mod.ccall('Z3_model_get_func_interp', 'number', ['number', 'number', 'number'], [c, m, f]);
                if (ret === 0) {
                    return null;
                }
                return ret;
            },
            model_get_num_consts: function (c, m) {
                let ret = Mod.ccall('Z3_model_get_num_consts', 'number', ['number', 'number'], [c, m]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            model_get_const_decl: Mod._Z3_model_get_const_decl,
            model_get_num_funcs: function (c, m) {
                let ret = Mod.ccall('Z3_model_get_num_funcs', 'number', ['number', 'number'], [c, m]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            model_get_func_decl: Mod._Z3_model_get_func_decl,
            model_get_num_sorts: function (c, m) {
                let ret = Mod.ccall('Z3_model_get_num_sorts', 'number', ['number', 'number'], [c, m]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            model_get_sort: Mod._Z3_model_get_sort,
            model_get_sort_universe: Mod._Z3_model_get_sort_universe,
            model_translate: Mod._Z3_model_translate,
            is_as_array: function (c, a) {
                return Mod.ccall('Z3_is_as_array', 'boolean', ['number', 'number'], [c, a]);
            },
            get_as_array_func_decl: Mod._Z3_get_as_array_func_decl,
            add_func_interp: Mod._Z3_add_func_interp,
            add_const_interp: Mod._Z3_add_const_interp,
            func_interp_inc_ref: Mod._Z3_func_interp_inc_ref,
            func_interp_dec_ref: Mod._Z3_func_interp_dec_ref,
            func_interp_get_num_entries: function (c, f) {
                let ret = Mod.ccall('Z3_func_interp_get_num_entries', 'number', ['number', 'number'], [c, f]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            func_interp_get_entry: Mod._Z3_func_interp_get_entry,
            func_interp_get_else: Mod._Z3_func_interp_get_else,
            func_interp_set_else: Mod._Z3_func_interp_set_else,
            func_interp_get_arity: function (c, f) {
                let ret = Mod.ccall('Z3_func_interp_get_arity', 'number', ['number', 'number'], [c, f]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            func_interp_add_entry: Mod._Z3_func_interp_add_entry,
            func_entry_inc_ref: Mod._Z3_func_entry_inc_ref,
            func_entry_dec_ref: Mod._Z3_func_entry_dec_ref,
            func_entry_get_value: Mod._Z3_func_entry_get_value,
            func_entry_get_num_args: function (c, e) {
                let ret = Mod.ccall('Z3_func_entry_get_num_args', 'number', ['number', 'number'], [c, e]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            func_entry_get_arg: Mod._Z3_func_entry_get_arg,
            open_log: function (filename) {
                return Mod.ccall('Z3_open_log', 'boolean', ['string'], [filename]);
            },
            append_log: function (string) {
                return Mod.ccall('Z3_append_log', 'void', ['string'], [string]);
            },
            close_log: Mod._Z3_close_log,
            toggle_warning_messages: Mod._Z3_toggle_warning_messages,
            set_ast_print_mode: Mod._Z3_set_ast_print_mode,
            ast_to_string: function (c, a) {
                return Mod.ccall('Z3_ast_to_string', 'string', ['number', 'number'], [c, a]);
            },
            pattern_to_string: function (c, p) {
                return Mod.ccall('Z3_pattern_to_string', 'string', ['number', 'number'], [c, p]);
            },
            sort_to_string: function (c, s) {
                return Mod.ccall('Z3_sort_to_string', 'string', ['number', 'number'], [c, s]);
            },
            func_decl_to_string: function (c, d) {
                return Mod.ccall('Z3_func_decl_to_string', 'string', ['number', 'number'], [c, d]);
            },
            model_to_string: function (c, m) {
                return Mod.ccall('Z3_model_to_string', 'string', ['number', 'number'], [c, m]);
            },
            benchmark_to_smtlib_string: function (c, name, logic, status, attributes, assumptions, formula) {
                return Mod.ccall('Z3_benchmark_to_smtlib_string', 'string', [
                    'number',
                    'string',
                    'string',
                    'string',
                    'string',
                    'number',
                    'array',
                    'number',
                ], [
                    c,
                    name,
                    logic,
                    status,
                    attributes,
                    assumptions.length,
                    intArrayToByteArr(assumptions),
                    formula,
                ]);
            },
            parse_smtlib2_string: function (c, str, sort_names, sorts, decl_names, decls) {
                if (sort_names.length !== sorts.length) {
                    throw new TypeError(`sort_names and sorts must be the same length (got ${sort_names.length} and {sorts.length})`);
                }
                if (decl_names.length !== decls.length) {
                    throw new TypeError(`decl_names and decls must be the same length (got ${decl_names.length} and {decls.length})`);
                }
                return Mod.ccall('Z3_parse_smtlib2_string', 'number', [
                    'number',
                    'string',
                    'number',
                    'array',
                    'array',
                    'number',
                    'array',
                    'array',
                ], [
                    c,
                    str,
                    sort_names.length,
                    intArrayToByteArr(sort_names),
                    intArrayToByteArr(sorts),
                    decl_names.length,
                    intArrayToByteArr(decl_names),
                    intArrayToByteArr(decls),
                ]);
            },
            parse_smtlib2_file: function (c, file_name, sort_names, sorts, decl_names, decls) {
                if (sort_names.length !== sorts.length) {
                    throw new TypeError(`sort_names and sorts must be the same length (got ${sort_names.length} and {sorts.length})`);
                }
                if (decl_names.length !== decls.length) {
                    throw new TypeError(`decl_names and decls must be the same length (got ${decl_names.length} and {decls.length})`);
                }
                return Mod.ccall('Z3_parse_smtlib2_file', 'number', [
                    'number',
                    'string',
                    'number',
                    'array',
                    'array',
                    'number',
                    'array',
                    'array',
                ], [
                    c,
                    file_name,
                    sort_names.length,
                    intArrayToByteArr(sort_names),
                    intArrayToByteArr(sorts),
                    decl_names.length,
                    intArrayToByteArr(decl_names),
                    intArrayToByteArr(decls),
                ]);
            },
            eval_smtlib2_string: async function (c, str) {
                return await Mod.async_call(() => Mod.ccall('async_Z3_eval_smtlib2_string', 'string', ['number', 'string'], [c, str]));
            },
            mk_parser_context: Mod._Z3_mk_parser_context,
            parser_context_inc_ref: Mod._Z3_parser_context_inc_ref,
            parser_context_dec_ref: Mod._Z3_parser_context_dec_ref,
            parser_context_add_sort: Mod._Z3_parser_context_add_sort,
            parser_context_add_decl: Mod._Z3_parser_context_add_decl,
            parser_context_from_string: function (c, pc, s) {
                return Mod.ccall('Z3_parser_context_from_string', 'number', ['number', 'number', 'string'], [c, pc, s]);
            },
            get_error_code: Mod._Z3_get_error_code,
            set_error: Mod._Z3_set_error,
            get_error_msg: function (c, err) {
                return Mod.ccall('Z3_get_error_msg', 'string', ['number', 'number'], [c, err]);
            },
            get_version: function () {
                let ret = Mod.ccall('Z3_get_version', 'void', ['number', 'number', 'number', 'number'], [outAddress, outAddress + 4, outAddress + 8, outAddress + 12]);
                return {
                    major: getOutUint(0),
                    minor: getOutUint(1),
                    build_number: getOutUint(2),
                    revision_number: getOutUint(3),
                };
            },
            get_full_version: function () {
                return Mod.ccall('Z3_get_full_version', 'string', [], []);
            },
            enable_trace: function (tag) {
                return Mod.ccall('Z3_enable_trace', 'void', ['string'], [tag]);
            },
            disable_trace: function (tag) {
                return Mod.ccall('Z3_disable_trace', 'void', ['string'], [tag]);
            },
            reset_memory: Mod._Z3_reset_memory,
            finalize_memory: Mod._Z3_finalize_memory,
            mk_goal: Mod._Z3_mk_goal,
            goal_inc_ref: Mod._Z3_goal_inc_ref,
            goal_dec_ref: Mod._Z3_goal_dec_ref,
            goal_precision: Mod._Z3_goal_precision,
            goal_assert: Mod._Z3_goal_assert,
            goal_inconsistent: function (c, g) {
                return Mod.ccall('Z3_goal_inconsistent', 'boolean', ['number', 'number'], [c, g]);
            },
            goal_depth: function (c, g) {
                let ret = Mod.ccall('Z3_goal_depth', 'number', ['number', 'number'], [c, g]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            goal_reset: Mod._Z3_goal_reset,
            goal_size: function (c, g) {
                let ret = Mod.ccall('Z3_goal_size', 'number', ['number', 'number'], [c, g]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            goal_formula: Mod._Z3_goal_formula,
            goal_num_exprs: function (c, g) {
                let ret = Mod.ccall('Z3_goal_num_exprs', 'number', ['number', 'number'], [c, g]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            goal_is_decided_sat: function (c, g) {
                return Mod.ccall('Z3_goal_is_decided_sat', 'boolean', ['number', 'number'], [c, g]);
            },
            goal_is_decided_unsat: function (c, g) {
                return Mod.ccall('Z3_goal_is_decided_unsat', 'boolean', ['number', 'number'], [c, g]);
            },
            goal_translate: Mod._Z3_goal_translate,
            goal_convert_model: Mod._Z3_goal_convert_model,
            goal_to_string: function (c, g) {
                return Mod.ccall('Z3_goal_to_string', 'string', ['number', 'number'], [c, g]);
            },
            goal_to_dimacs_string: function (c, g, include_names) {
                return Mod.ccall('Z3_goal_to_dimacs_string', 'string', ['number', 'number', 'boolean'], [c, g, include_names]);
            },
            mk_tactic: function (c, name) {
                return Mod.ccall('Z3_mk_tactic', 'number', ['number', 'string'], [c, name]);
            },
            tactic_inc_ref: Mod._Z3_tactic_inc_ref,
            tactic_dec_ref: Mod._Z3_tactic_dec_ref,
            mk_probe: function (c, name) {
                return Mod.ccall('Z3_mk_probe', 'number', ['number', 'string'], [c, name]);
            },
            probe_inc_ref: Mod._Z3_probe_inc_ref,
            probe_dec_ref: Mod._Z3_probe_dec_ref,
            tactic_and_then: Mod._Z3_tactic_and_then,
            tactic_or_else: Mod._Z3_tactic_or_else,
            tactic_par_or: function (c, ts) {
                return Mod.ccall('Z3_tactic_par_or', 'number', ['number', 'number', 'array'], [c, ts.length, intArrayToByteArr(ts)]);
            },
            tactic_par_and_then: Mod._Z3_tactic_par_and_then,
            tactic_try_for: Mod._Z3_tactic_try_for,
            tactic_when: Mod._Z3_tactic_when,
            tactic_cond: Mod._Z3_tactic_cond,
            tactic_repeat: Mod._Z3_tactic_repeat,
            tactic_skip: Mod._Z3_tactic_skip,
            tactic_fail: Mod._Z3_tactic_fail,
            tactic_fail_if: Mod._Z3_tactic_fail_if,
            tactic_fail_if_not_decided: Mod._Z3_tactic_fail_if_not_decided,
            tactic_using_params: Mod._Z3_tactic_using_params,
            mk_simplifier: function (c, name) {
                return Mod.ccall('Z3_mk_simplifier', 'number', ['number', 'string'], [c, name]);
            },
            simplifier_inc_ref: Mod._Z3_simplifier_inc_ref,
            simplifier_dec_ref: Mod._Z3_simplifier_dec_ref,
            solver_add_simplifier: Mod._Z3_solver_add_simplifier,
            simplifier_and_then: Mod._Z3_simplifier_and_then,
            simplifier_using_params: Mod._Z3_simplifier_using_params,
            get_num_simplifiers: function (c) {
                let ret = Mod.ccall('Z3_get_num_simplifiers', 'number', ['number'], [c]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_simplifier_name: function (c, i) {
                return Mod.ccall('Z3_get_simplifier_name', 'string', ['number', 'number'], [c, i]);
            },
            simplifier_get_help: function (c, t) {
                return Mod.ccall('Z3_simplifier_get_help', 'string', ['number', 'number'], [c, t]);
            },
            simplifier_get_param_descrs: Mod._Z3_simplifier_get_param_descrs,
            simplifier_get_descr: function (c, name) {
                return Mod.ccall('Z3_simplifier_get_descr', 'string', ['number', 'string'], [c, name]);
            },
            probe_const: Mod._Z3_probe_const,
            probe_lt: Mod._Z3_probe_lt,
            probe_gt: Mod._Z3_probe_gt,
            probe_le: Mod._Z3_probe_le,
            probe_ge: Mod._Z3_probe_ge,
            probe_eq: Mod._Z3_probe_eq,
            probe_and: Mod._Z3_probe_and,
            probe_or: Mod._Z3_probe_or,
            probe_not: Mod._Z3_probe_not,
            get_num_tactics: function (c) {
                let ret = Mod.ccall('Z3_get_num_tactics', 'number', ['number'], [c]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_tactic_name: function (c, i) {
                return Mod.ccall('Z3_get_tactic_name', 'string', ['number', 'number'], [c, i]);
            },
            get_num_probes: function (c) {
                let ret = Mod.ccall('Z3_get_num_probes', 'number', ['number'], [c]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            get_probe_name: function (c, i) {
                return Mod.ccall('Z3_get_probe_name', 'string', ['number', 'number'], [c, i]);
            },
            tactic_get_help: function (c, t) {
                return Mod.ccall('Z3_tactic_get_help', 'string', ['number', 'number'], [c, t]);
            },
            tactic_get_param_descrs: Mod._Z3_tactic_get_param_descrs,
            tactic_get_descr: function (c, name) {
                return Mod.ccall('Z3_tactic_get_descr', 'string', ['number', 'string'], [c, name]);
            },
            probe_get_descr: function (c, name) {
                return Mod.ccall('Z3_probe_get_descr', 'string', ['number', 'string'], [c, name]);
            },
            probe_apply: Mod._Z3_probe_apply,
            tactic_apply: function (c, t, g) {
                return Mod.async_call(Mod._async_Z3_tactic_apply, c, t, g);
            },
            tactic_apply_ex: function (c, t, g, p) {
                return Mod.async_call(Mod._async_Z3_tactic_apply_ex, c, t, g, p);
            },
            apply_result_inc_ref: Mod._Z3_apply_result_inc_ref,
            apply_result_dec_ref: Mod._Z3_apply_result_dec_ref,
            apply_result_to_string: function (c, r) {
                return Mod.ccall('Z3_apply_result_to_string', 'string', ['number', 'number'], [c, r]);
            },
            apply_result_get_num_subgoals: function (c, r) {
                let ret = Mod.ccall('Z3_apply_result_get_num_subgoals', 'number', ['number', 'number'], [c, r]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            apply_result_get_subgoal: Mod._Z3_apply_result_get_subgoal,
            mk_solver: Mod._Z3_mk_solver,
            mk_simple_solver: Mod._Z3_mk_simple_solver,
            mk_solver_for_logic: Mod._Z3_mk_solver_for_logic,
            mk_solver_from_tactic: Mod._Z3_mk_solver_from_tactic,
            solver_translate: Mod._Z3_solver_translate,
            solver_import_model_converter: Mod._Z3_solver_import_model_converter,
            solver_get_help: function (c, s) {
                return Mod.ccall('Z3_solver_get_help', 'string', ['number', 'number'], [c, s]);
            },
            solver_get_param_descrs: Mod._Z3_solver_get_param_descrs,
            solver_set_params: Mod._Z3_solver_set_params,
            solver_inc_ref: Mod._Z3_solver_inc_ref,
            solver_dec_ref: Mod._Z3_solver_dec_ref,
            solver_interrupt: Mod._Z3_solver_interrupt,
            solver_push: Mod._Z3_solver_push,
            solver_pop: Mod._Z3_solver_pop,
            solver_reset: Mod._Z3_solver_reset,
            solver_get_num_scopes: function (c, s) {
                let ret = Mod.ccall('Z3_solver_get_num_scopes', 'number', ['number', 'number'], [c, s]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            solver_assert: Mod._Z3_solver_assert,
            solver_assert_and_track: Mod._Z3_solver_assert_and_track,
            solver_from_file: function (c, s, file_name) {
                return Mod.ccall('Z3_solver_from_file', 'void', ['number', 'number', 'string'], [c, s, file_name]);
            },
            solver_from_string: function (c, s, file_name) {
                return Mod.ccall('Z3_solver_from_string', 'void', ['number', 'number', 'string'], [c, s, file_name]);
            },
            solver_get_assertions: Mod._Z3_solver_get_assertions,
            solver_get_units: Mod._Z3_solver_get_units,
            solver_get_trail: Mod._Z3_solver_get_trail,
            solver_get_non_units: Mod._Z3_solver_get_non_units,
            solver_get_levels: function (c, s, literals, levels) {
                return Mod.ccall('Z3_solver_get_levels', 'void', ['number', 'number', 'number', 'number', 'array'], [
                    c,
                    s,
                    literals,
                    levels.length,
                    intArrayToByteArr(levels),
                ]);
            },
            solver_congruence_root: Mod._Z3_solver_congruence_root,
            solver_congruence_next: Mod._Z3_solver_congruence_next,
            solver_next_split: function (c, cb, t, idx, phase) {
                return Mod.ccall('Z3_solver_next_split', 'boolean', ['number', 'number', 'number', 'number', 'number'], [c, cb, t, idx, phase]);
            },
            solver_propagate_declare: function (c, name, domain, range) {
                return Mod.ccall('Z3_solver_propagate_declare', 'number', ['number', 'number', 'number', 'array', 'number'], [
                    c,
                    name,
                    domain.length,
                    intArrayToByteArr(domain),
                    range,
                ]);
            },
            solver_propagate_register: Mod._Z3_solver_propagate_register,
            solver_propagate_register_cb: Mod._Z3_solver_propagate_register_cb,
            solver_propagate_consequence: function (c, cb, fixed, eq_lhs, eq_rhs, conseq) {
                if (eq_lhs.length !== eq_rhs.length) {
                    throw new TypeError(`eq_lhs and eq_rhs must be the same length (got ${eq_lhs.length} and {eq_rhs.length})`);
                }
                return Mod.ccall('Z3_solver_propagate_consequence', 'boolean', [
                    'number',
                    'number',
                    'number',
                    'array',
                    'number',
                    'array',
                    'array',
                    'number',
                ], [
                    c,
                    cb,
                    fixed.length,
                    intArrayToByteArr(fixed),
                    eq_lhs.length,
                    intArrayToByteArr(eq_lhs),
                    intArrayToByteArr(eq_rhs),
                    conseq,
                ]);
            },
            solver_check: function (c, s) {
                return Mod.async_call(Mod._async_Z3_solver_check, c, s);
            },
            solver_check_assumptions: async function (c, s, assumptions) {
                return await Mod.async_call(() => Mod.ccall('async_Z3_solver_check_assumptions', 'number', ['number', 'number', 'number', 'array'], [
                    c,
                    s,
                    assumptions.length,
                    intArrayToByteArr(assumptions),
                ]));
            },
            get_implied_equalities: function (c, s, terms) {
                let outArray_class_ids = Mod._malloc(4 * terms.length);
                try {
                    let ret = Mod.ccall('Z3_get_implied_equalities', 'number', ['number', 'number', 'number', 'array', 'number'], [
                        c,
                        s,
                        terms.length,
                        intArrayToByteArr(terms),
                        outArray_class_ids,
                    ]);
                    return {
                        rv: ret,
                        class_ids: readUintArray(outArray_class_ids, terms.length),
                    };
                }
                finally {
                    Mod._free(outArray_class_ids);
                }
            },
            solver_get_consequences: function (c, s, assumptions, variables, consequences) {
                return Mod.async_call(Mod._async_Z3_solver_get_consequences, c, s, assumptions, variables, consequences);
            },
            solver_cube: function (c, s, vars, backtrack_level) {
                return Mod.async_call(Mod._async_Z3_solver_cube, c, s, vars, backtrack_level);
            },
            solver_get_model: Mod._Z3_solver_get_model,
            solver_get_proof: Mod._Z3_solver_get_proof,
            solver_get_unsat_core: Mod._Z3_solver_get_unsat_core,
            solver_get_reason_unknown: function (c, s) {
                return Mod.ccall('Z3_solver_get_reason_unknown', 'string', ['number', 'number'], [c, s]);
            },
            solver_get_statistics: Mod._Z3_solver_get_statistics,
            solver_to_string: function (c, s) {
                return Mod.ccall('Z3_solver_to_string', 'string', ['number', 'number'], [c, s]);
            },
            solver_to_dimacs_string: function (c, s, include_names) {
                return Mod.ccall('Z3_solver_to_dimacs_string', 'string', ['number', 'number', 'boolean'], [c, s, include_names]);
            },
            stats_to_string: function (c, s) {
                return Mod.ccall('Z3_stats_to_string', 'string', ['number', 'number'], [c, s]);
            },
            stats_inc_ref: Mod._Z3_stats_inc_ref,
            stats_dec_ref: Mod._Z3_stats_dec_ref,
            stats_size: function (c, s) {
                let ret = Mod.ccall('Z3_stats_size', 'number', ['number', 'number'], [c, s]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            stats_get_key: function (c, s, idx) {
                return Mod.ccall('Z3_stats_get_key', 'string', ['number', 'number', 'number'], [c, s, idx]);
            },
            stats_is_uint: function (c, s, idx) {
                return Mod.ccall('Z3_stats_is_uint', 'boolean', ['number', 'number', 'number'], [c, s, idx]);
            },
            stats_is_double: function (c, s, idx) {
                return Mod.ccall('Z3_stats_is_double', 'boolean', ['number', 'number', 'number'], [c, s, idx]);
            },
            stats_get_uint_value: function (c, s, idx) {
                let ret = Mod.ccall('Z3_stats_get_uint_value', 'number', ['number', 'number', 'number'], [c, s, idx]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            stats_get_double_value: Mod._Z3_stats_get_double_value,
            get_estimated_alloc_size: Mod._Z3_get_estimated_alloc_size,
            algebraic_is_value: function (c, a) {
                return Mod.ccall('Z3_algebraic_is_value', 'boolean', ['number', 'number'], [c, a]);
            },
            algebraic_is_pos: function (c, a) {
                return Mod.ccall('Z3_algebraic_is_pos', 'boolean', ['number', 'number'], [c, a]);
            },
            algebraic_is_neg: function (c, a) {
                return Mod.ccall('Z3_algebraic_is_neg', 'boolean', ['number', 'number'], [c, a]);
            },
            algebraic_is_zero: function (c, a) {
                return Mod.ccall('Z3_algebraic_is_zero', 'boolean', ['number', 'number'], [c, a]);
            },
            algebraic_sign: Mod._Z3_algebraic_sign,
            algebraic_add: Mod._Z3_algebraic_add,
            algebraic_sub: Mod._Z3_algebraic_sub,
            algebraic_mul: Mod._Z3_algebraic_mul,
            algebraic_div: Mod._Z3_algebraic_div,
            algebraic_root: Mod._Z3_algebraic_root,
            algebraic_power: Mod._Z3_algebraic_power,
            algebraic_lt: function (c, a, b) {
                return Mod.ccall('Z3_algebraic_lt', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            algebraic_gt: function (c, a, b) {
                return Mod.ccall('Z3_algebraic_gt', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            algebraic_le: function (c, a, b) {
                return Mod.ccall('Z3_algebraic_le', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            algebraic_ge: function (c, a, b) {
                return Mod.ccall('Z3_algebraic_ge', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            algebraic_eq: function (c, a, b) {
                return Mod.ccall('Z3_algebraic_eq', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            algebraic_neq: function (c, a, b) {
                return Mod.ccall('Z3_algebraic_neq', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            algebraic_roots: async function (c, p, a) {
                return await Mod.async_call(() => Mod.ccall('async_Z3_algebraic_roots', 'number', ['number', 'number', 'number', 'array'], [c, p, a.length, intArrayToByteArr(a)]));
            },
            algebraic_eval: async function (c, p, a) {
                return await Mod.async_call(() => Mod.ccall('async_Z3_algebraic_eval', 'number', ['number', 'number', 'number', 'array'], [c, p, a.length, intArrayToByteArr(a)]));
            },
            algebraic_get_poly: Mod._Z3_algebraic_get_poly,
            algebraic_get_i: function (c, a) {
                let ret = Mod.ccall('Z3_algebraic_get_i', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            mk_ast_vector: Mod._Z3_mk_ast_vector,
            ast_vector_inc_ref: Mod._Z3_ast_vector_inc_ref,
            ast_vector_dec_ref: Mod._Z3_ast_vector_dec_ref,
            ast_vector_size: function (c, v) {
                let ret = Mod.ccall('Z3_ast_vector_size', 'number', ['number', 'number'], [c, v]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            ast_vector_get: Mod._Z3_ast_vector_get,
            ast_vector_set: Mod._Z3_ast_vector_set,
            ast_vector_resize: Mod._Z3_ast_vector_resize,
            ast_vector_push: Mod._Z3_ast_vector_push,
            ast_vector_translate: Mod._Z3_ast_vector_translate,
            ast_vector_to_string: function (c, v) {
                return Mod.ccall('Z3_ast_vector_to_string', 'string', ['number', 'number'], [c, v]);
            },
            mk_ast_map: Mod._Z3_mk_ast_map,
            ast_map_inc_ref: Mod._Z3_ast_map_inc_ref,
            ast_map_dec_ref: Mod._Z3_ast_map_dec_ref,
            ast_map_contains: function (c, m, k) {
                return Mod.ccall('Z3_ast_map_contains', 'boolean', ['number', 'number', 'number'], [c, m, k]);
            },
            ast_map_find: Mod._Z3_ast_map_find,
            ast_map_insert: Mod._Z3_ast_map_insert,
            ast_map_erase: Mod._Z3_ast_map_erase,
            ast_map_reset: Mod._Z3_ast_map_reset,
            ast_map_size: function (c, m) {
                let ret = Mod.ccall('Z3_ast_map_size', 'number', ['number', 'number'], [c, m]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            ast_map_keys: Mod._Z3_ast_map_keys,
            ast_map_to_string: function (c, m) {
                return Mod.ccall('Z3_ast_map_to_string', 'string', ['number', 'number'], [c, m]);
            },
            mk_fixedpoint: Mod._Z3_mk_fixedpoint,
            fixedpoint_inc_ref: Mod._Z3_fixedpoint_inc_ref,
            fixedpoint_dec_ref: Mod._Z3_fixedpoint_dec_ref,
            fixedpoint_add_rule: Mod._Z3_fixedpoint_add_rule,
            fixedpoint_add_fact: function (c, d, r, args) {
                return Mod.ccall('Z3_fixedpoint_add_fact', 'void', ['number', 'number', 'number', 'number', 'array'], [c, d, r, args.length, intArrayToByteArr(args)]);
            },
            fixedpoint_assert: Mod._Z3_fixedpoint_assert,
            fixedpoint_query: function (c, d, query) {
                return Mod.async_call(Mod._async_Z3_fixedpoint_query, c, d, query);
            },
            fixedpoint_query_relations: async function (c, d, relations) {
                return await Mod.async_call(() => Mod.ccall('async_Z3_fixedpoint_query_relations', 'number', ['number', 'number', 'number', 'array'], [
                    c,
                    d,
                    relations.length,
                    intArrayToByteArr(relations),
                ]));
            },
            fixedpoint_get_answer: Mod._Z3_fixedpoint_get_answer,
            fixedpoint_get_reason_unknown: function (c, d) {
                return Mod.ccall('Z3_fixedpoint_get_reason_unknown', 'string', ['number', 'number'], [c, d]);
            },
            fixedpoint_update_rule: Mod._Z3_fixedpoint_update_rule,
            fixedpoint_get_num_levels: function (c, d, pred) {
                let ret = Mod.ccall('Z3_fixedpoint_get_num_levels', 'number', ['number', 'number', 'number'], [c, d, pred]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            fixedpoint_get_cover_delta: Mod._Z3_fixedpoint_get_cover_delta,
            fixedpoint_add_cover: Mod._Z3_fixedpoint_add_cover,
            fixedpoint_get_statistics: Mod._Z3_fixedpoint_get_statistics,
            fixedpoint_register_relation: Mod._Z3_fixedpoint_register_relation,
            fixedpoint_set_predicate_representation: function (c, d, f, relation_kinds) {
                return Mod.ccall('Z3_fixedpoint_set_predicate_representation', 'void', ['number', 'number', 'number', 'number', 'array'], [
                    c,
                    d,
                    f,
                    relation_kinds.length,
                    intArrayToByteArr(relation_kinds),
                ]);
            },
            fixedpoint_get_rules: Mod._Z3_fixedpoint_get_rules,
            fixedpoint_get_assertions: Mod._Z3_fixedpoint_get_assertions,
            fixedpoint_set_params: Mod._Z3_fixedpoint_set_params,
            fixedpoint_get_help: function (c, f) {
                return Mod.ccall('Z3_fixedpoint_get_help', 'string', ['number', 'number'], [c, f]);
            },
            fixedpoint_get_param_descrs: Mod._Z3_fixedpoint_get_param_descrs,
            fixedpoint_to_string: function (c, f, queries) {
                return Mod.ccall('Z3_fixedpoint_to_string', 'string', ['number', 'number', 'number', 'array'], [
                    c,
                    f,
                    queries.length,
                    intArrayToByteArr(queries),
                ]);
            },
            fixedpoint_from_string: function (c, f, s) {
                return Mod.ccall('Z3_fixedpoint_from_string', 'number', ['number', 'number', 'string'], [c, f, s]);
            },
            fixedpoint_from_file: function (c, f, s) {
                return Mod.ccall('Z3_fixedpoint_from_file', 'number', ['number', 'number', 'string'], [c, f, s]);
            },
            mk_fpa_rounding_mode_sort: Mod._Z3_mk_fpa_rounding_mode_sort,
            mk_fpa_round_nearest_ties_to_even: Mod._Z3_mk_fpa_round_nearest_ties_to_even,
            mk_fpa_rne: Mod._Z3_mk_fpa_rne,
            mk_fpa_round_nearest_ties_to_away: Mod._Z3_mk_fpa_round_nearest_ties_to_away,
            mk_fpa_rna: Mod._Z3_mk_fpa_rna,
            mk_fpa_round_toward_positive: Mod._Z3_mk_fpa_round_toward_positive,
            mk_fpa_rtp: Mod._Z3_mk_fpa_rtp,
            mk_fpa_round_toward_negative: Mod._Z3_mk_fpa_round_toward_negative,
            mk_fpa_rtn: Mod._Z3_mk_fpa_rtn,
            mk_fpa_round_toward_zero: Mod._Z3_mk_fpa_round_toward_zero,
            mk_fpa_rtz: Mod._Z3_mk_fpa_rtz,
            mk_fpa_sort: Mod._Z3_mk_fpa_sort,
            mk_fpa_sort_half: Mod._Z3_mk_fpa_sort_half,
            mk_fpa_sort_16: Mod._Z3_mk_fpa_sort_16,
            mk_fpa_sort_single: Mod._Z3_mk_fpa_sort_single,
            mk_fpa_sort_32: Mod._Z3_mk_fpa_sort_32,
            mk_fpa_sort_double: Mod._Z3_mk_fpa_sort_double,
            mk_fpa_sort_64: Mod._Z3_mk_fpa_sort_64,
            mk_fpa_sort_quadruple: Mod._Z3_mk_fpa_sort_quadruple,
            mk_fpa_sort_128: Mod._Z3_mk_fpa_sort_128,
            mk_fpa_nan: Mod._Z3_mk_fpa_nan,
            mk_fpa_inf: Mod._Z3_mk_fpa_inf,
            mk_fpa_zero: Mod._Z3_mk_fpa_zero,
            mk_fpa_fp: Mod._Z3_mk_fpa_fp,
            mk_fpa_numeral_float: Mod._Z3_mk_fpa_numeral_float,
            mk_fpa_numeral_double: Mod._Z3_mk_fpa_numeral_double,
            mk_fpa_numeral_int: Mod._Z3_mk_fpa_numeral_int,
            mk_fpa_numeral_int_uint: Mod._Z3_mk_fpa_numeral_int_uint,
            mk_fpa_numeral_int64_uint64: Mod._Z3_mk_fpa_numeral_int64_uint64,
            mk_fpa_abs: Mod._Z3_mk_fpa_abs,
            mk_fpa_neg: Mod._Z3_mk_fpa_neg,
            mk_fpa_add: Mod._Z3_mk_fpa_add,
            mk_fpa_sub: Mod._Z3_mk_fpa_sub,
            mk_fpa_mul: Mod._Z3_mk_fpa_mul,
            mk_fpa_div: Mod._Z3_mk_fpa_div,
            mk_fpa_fma: Mod._Z3_mk_fpa_fma,
            mk_fpa_sqrt: Mod._Z3_mk_fpa_sqrt,
            mk_fpa_rem: Mod._Z3_mk_fpa_rem,
            mk_fpa_round_to_integral: Mod._Z3_mk_fpa_round_to_integral,
            mk_fpa_min: Mod._Z3_mk_fpa_min,
            mk_fpa_max: Mod._Z3_mk_fpa_max,
            mk_fpa_leq: Mod._Z3_mk_fpa_leq,
            mk_fpa_lt: Mod._Z3_mk_fpa_lt,
            mk_fpa_geq: Mod._Z3_mk_fpa_geq,
            mk_fpa_gt: Mod._Z3_mk_fpa_gt,
            mk_fpa_eq: Mod._Z3_mk_fpa_eq,
            mk_fpa_is_normal: Mod._Z3_mk_fpa_is_normal,
            mk_fpa_is_subnormal: Mod._Z3_mk_fpa_is_subnormal,
            mk_fpa_is_zero: Mod._Z3_mk_fpa_is_zero,
            mk_fpa_is_infinite: Mod._Z3_mk_fpa_is_infinite,
            mk_fpa_is_nan: Mod._Z3_mk_fpa_is_nan,
            mk_fpa_is_negative: Mod._Z3_mk_fpa_is_negative,
            mk_fpa_is_positive: Mod._Z3_mk_fpa_is_positive,
            mk_fpa_to_fp_bv: Mod._Z3_mk_fpa_to_fp_bv,
            mk_fpa_to_fp_float: Mod._Z3_mk_fpa_to_fp_float,
            mk_fpa_to_fp_real: Mod._Z3_mk_fpa_to_fp_real,
            mk_fpa_to_fp_signed: Mod._Z3_mk_fpa_to_fp_signed,
            mk_fpa_to_fp_unsigned: Mod._Z3_mk_fpa_to_fp_unsigned,
            mk_fpa_to_ubv: Mod._Z3_mk_fpa_to_ubv,
            mk_fpa_to_sbv: Mod._Z3_mk_fpa_to_sbv,
            mk_fpa_to_real: Mod._Z3_mk_fpa_to_real,
            fpa_get_ebits: function (c, s) {
                let ret = Mod.ccall('Z3_fpa_get_ebits', 'number', ['number', 'number'], [c, s]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            fpa_get_sbits: function (c, s) {
                let ret = Mod.ccall('Z3_fpa_get_sbits', 'number', ['number', 'number'], [c, s]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            fpa_is_numeral_nan: function (c, t) {
                return Mod.ccall('Z3_fpa_is_numeral_nan', 'boolean', ['number', 'number'], [c, t]);
            },
            fpa_is_numeral_inf: function (c, t) {
                return Mod.ccall('Z3_fpa_is_numeral_inf', 'boolean', ['number', 'number'], [c, t]);
            },
            fpa_is_numeral_zero: function (c, t) {
                return Mod.ccall('Z3_fpa_is_numeral_zero', 'boolean', ['number', 'number'], [c, t]);
            },
            fpa_is_numeral_normal: function (c, t) {
                return Mod.ccall('Z3_fpa_is_numeral_normal', 'boolean', ['number', 'number'], [c, t]);
            },
            fpa_is_numeral_subnormal: function (c, t) {
                return Mod.ccall('Z3_fpa_is_numeral_subnormal', 'boolean', ['number', 'number'], [c, t]);
            },
            fpa_is_numeral_positive: function (c, t) {
                return Mod.ccall('Z3_fpa_is_numeral_positive', 'boolean', ['number', 'number'], [c, t]);
            },
            fpa_is_numeral_negative: function (c, t) {
                return Mod.ccall('Z3_fpa_is_numeral_negative', 'boolean', ['number', 'number'], [c, t]);
            },
            fpa_get_numeral_sign_bv: Mod._Z3_fpa_get_numeral_sign_bv,
            fpa_get_numeral_significand_bv: Mod._Z3_fpa_get_numeral_significand_bv,
            fpa_get_numeral_sign: function (c, t) {
                let ret = Mod.ccall('Z3_fpa_get_numeral_sign', 'boolean', ['number', 'number', 'number'], [c, t, outAddress]);
                if (!ret) {
                    return null;
                }
                return getOutInt(0);
            },
            fpa_get_numeral_significand_string: function (c, t) {
                return Mod.ccall('Z3_fpa_get_numeral_significand_string', 'string', ['number', 'number'], [c, t]);
            },
            fpa_get_numeral_significand_uint64: function (c, t) {
                let ret = Mod.ccall('Z3_fpa_get_numeral_significand_uint64', 'boolean', ['number', 'number', 'number'], [c, t, outAddress]);
                if (!ret) {
                    return null;
                }
                return getOutUint64(0);
            },
            fpa_get_numeral_exponent_string: function (c, t, biased) {
                return Mod.ccall('Z3_fpa_get_numeral_exponent_string', 'string', ['number', 'number', 'boolean'], [c, t, biased]);
            },
            fpa_get_numeral_exponent_int64: function (c, t, biased) {
                let ret = Mod.ccall('Z3_fpa_get_numeral_exponent_int64', 'boolean', ['number', 'number', 'number', 'boolean'], [c, t, outAddress, biased]);
                if (!ret) {
                    return null;
                }
                return getOutInt64(0);
            },
            fpa_get_numeral_exponent_bv: Mod._Z3_fpa_get_numeral_exponent_bv,
            mk_fpa_to_ieee_bv: Mod._Z3_mk_fpa_to_ieee_bv,
            mk_fpa_to_fp_int_real: Mod._Z3_mk_fpa_to_fp_int_real,
            mk_optimize: Mod._Z3_mk_optimize,
            optimize_inc_ref: Mod._Z3_optimize_inc_ref,
            optimize_dec_ref: Mod._Z3_optimize_dec_ref,
            optimize_assert: Mod._Z3_optimize_assert,
            optimize_assert_and_track: Mod._Z3_optimize_assert_and_track,
            optimize_assert_soft: function (c, o, a, weight, id) {
                let ret = Mod.ccall('Z3_optimize_assert_soft', 'number', ['number', 'number', 'number', 'string', 'number'], [c, o, a, weight, id]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            optimize_maximize: function (c, o, t) {
                let ret = Mod.ccall('Z3_optimize_maximize', 'number', ['number', 'number', 'number'], [c, o, t]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            optimize_minimize: function (c, o, t) {
                let ret = Mod.ccall('Z3_optimize_minimize', 'number', ['number', 'number', 'number'], [c, o, t]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            optimize_push: Mod._Z3_optimize_push,
            optimize_pop: Mod._Z3_optimize_pop,
            optimize_check: async function (c, o, assumptions) {
                return await Mod.async_call(() => Mod.ccall('async_Z3_optimize_check', 'number', ['number', 'number', 'number', 'array'], [
                    c,
                    o,
                    assumptions.length,
                    intArrayToByteArr(assumptions),
                ]));
            },
            optimize_get_reason_unknown: function (c, d) {
                return Mod.ccall('Z3_optimize_get_reason_unknown', 'string', ['number', 'number'], [c, d]);
            },
            optimize_get_model: Mod._Z3_optimize_get_model,
            optimize_get_unsat_core: Mod._Z3_optimize_get_unsat_core,
            optimize_set_params: Mod._Z3_optimize_set_params,
            optimize_get_param_descrs: Mod._Z3_optimize_get_param_descrs,
            optimize_get_lower: Mod._Z3_optimize_get_lower,
            optimize_get_upper: Mod._Z3_optimize_get_upper,
            optimize_get_lower_as_vector: Mod._Z3_optimize_get_lower_as_vector,
            optimize_get_upper_as_vector: Mod._Z3_optimize_get_upper_as_vector,
            optimize_to_string: function (c, o) {
                return Mod.ccall('Z3_optimize_to_string', 'string', ['number', 'number'], [c, o]);
            },
            optimize_from_string: function (c, o, s) {
                return Mod.ccall('Z3_optimize_from_string', 'void', ['number', 'number', 'string'], [c, o, s]);
            },
            optimize_from_file: function (c, o, s) {
                return Mod.ccall('Z3_optimize_from_file', 'void', ['number', 'number', 'string'], [c, o, s]);
            },
            optimize_get_help: function (c, t) {
                return Mod.ccall('Z3_optimize_get_help', 'string', ['number', 'number'], [c, t]);
            },
            optimize_get_statistics: Mod._Z3_optimize_get_statistics,
            optimize_get_assertions: Mod._Z3_optimize_get_assertions,
            optimize_get_objectives: Mod._Z3_optimize_get_objectives,
            polynomial_subresultants: function (c, p, q, x) {
                return Mod.async_call(Mod._async_Z3_polynomial_subresultants, c, p, q, x);
            },
            rcf_del: Mod._Z3_rcf_del,
            rcf_mk_rational: function (c, val) {
                return Mod.ccall('Z3_rcf_mk_rational', 'number', ['number', 'string'], [c, val]);
            },
            rcf_mk_small_int: Mod._Z3_rcf_mk_small_int,
            rcf_mk_pi: Mod._Z3_rcf_mk_pi,
            rcf_mk_e: Mod._Z3_rcf_mk_e,
            rcf_mk_infinitesimal: Mod._Z3_rcf_mk_infinitesimal,
            rcf_mk_roots: function (c, a) {
                let outArray_roots = Mod._malloc(4 * a.length);
                try {
                    let ret = Mod.ccall('Z3_rcf_mk_roots', 'number', ['number', 'number', 'array', 'number'], [
                        c,
                        a.length,
                        intArrayToByteArr(a),
                        outArray_roots,
                    ]);
                    ret = new Uint32Array([ret])[0];
                    return {
                        rv: ret,
                        roots: readUintArray(outArray_roots, a.length),
                    };
                }
                finally {
                    Mod._free(outArray_roots);
                }
            },
            rcf_add: Mod._Z3_rcf_add,
            rcf_sub: Mod._Z3_rcf_sub,
            rcf_mul: Mod._Z3_rcf_mul,
            rcf_div: Mod._Z3_rcf_div,
            rcf_neg: Mod._Z3_rcf_neg,
            rcf_inv: Mod._Z3_rcf_inv,
            rcf_power: Mod._Z3_rcf_power,
            rcf_lt: function (c, a, b) {
                return Mod.ccall('Z3_rcf_lt', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            rcf_gt: function (c, a, b) {
                return Mod.ccall('Z3_rcf_gt', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            rcf_le: function (c, a, b) {
                return Mod.ccall('Z3_rcf_le', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            rcf_ge: function (c, a, b) {
                return Mod.ccall('Z3_rcf_ge', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            rcf_eq: function (c, a, b) {
                return Mod.ccall('Z3_rcf_eq', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            rcf_neq: function (c, a, b) {
                return Mod.ccall('Z3_rcf_neq', 'boolean', ['number', 'number', 'number'], [c, a, b]);
            },
            rcf_num_to_string: function (c, a, compact, html) {
                return Mod.ccall('Z3_rcf_num_to_string', 'string', ['number', 'number', 'boolean', 'boolean'], [c, a, compact, html]);
            },
            rcf_num_to_decimal_string: function (c, a, prec) {
                return Mod.ccall('Z3_rcf_num_to_decimal_string', 'string', ['number', 'number', 'number'], [c, a, prec]);
            },
            rcf_get_numerator_denominator: function (c, a) {
                let ret = Mod.ccall('Z3_rcf_get_numerator_denominator', 'void', ['number', 'number', 'number', 'number'], [c, a, outAddress, outAddress + 4]);
                return {
                    n: getOutUint(0),
                    d: getOutUint(1),
                };
            },
            rcf_is_rational: function (c, a) {
                return Mod.ccall('Z3_rcf_is_rational', 'boolean', ['number', 'number'], [c, a]);
            },
            rcf_is_algebraic: function (c, a) {
                return Mod.ccall('Z3_rcf_is_algebraic', 'boolean', ['number', 'number'], [c, a]);
            },
            rcf_is_infinitesimal: function (c, a) {
                return Mod.ccall('Z3_rcf_is_infinitesimal', 'boolean', ['number', 'number'], [c, a]);
            },
            rcf_is_transcendental: function (c, a) {
                return Mod.ccall('Z3_rcf_is_transcendental', 'boolean', ['number', 'number'], [c, a]);
            },
            rcf_extension_index: function (c, a) {
                let ret = Mod.ccall('Z3_rcf_extension_index', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            rcf_transcendental_name: Mod._Z3_rcf_transcendental_name,
            rcf_infinitesimal_name: Mod._Z3_rcf_infinitesimal_name,
            rcf_num_coefficients: function (c, a) {
                let ret = Mod.ccall('Z3_rcf_num_coefficients', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            rcf_coefficient: Mod._Z3_rcf_coefficient,
            rcf_num_sign_conditions: function (c, a) {
                let ret = Mod.ccall('Z3_rcf_num_sign_conditions', 'number', ['number', 'number'], [c, a]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            rcf_sign_condition_sign: Mod._Z3_rcf_sign_condition_sign,
            rcf_num_sign_condition_coefficients: function (c, a, i) {
                let ret = Mod.ccall('Z3_rcf_num_sign_condition_coefficients', 'number', ['number', 'number', 'number'], [c, a, i]);
                ret = new Uint32Array([ret])[0];
                return ret;
            },
            rcf_sign_condition_coefficient: Mod._Z3_rcf_sign_condition_coefficient,
            fixedpoint_query_from_lvl: function (c, d, query, lvl) {
                return Mod.async_call(Mod._async_Z3_fixedpoint_query_from_lvl, c, d, query, lvl);
            },
            fixedpoint_get_ground_sat_answer: Mod._Z3_fixedpoint_get_ground_sat_answer,
            fixedpoint_get_rules_along_trace: Mod._Z3_fixedpoint_get_rules_along_trace,
            fixedpoint_get_rule_names_along_trace: Mod._Z3_fixedpoint_get_rule_names_along_trace,
            fixedpoint_add_invariant: Mod._Z3_fixedpoint_add_invariant,
            fixedpoint_get_reachable: Mod._Z3_fixedpoint_get_reachable,
            qe_model_project: function (c, m, bound, body) {
                return Mod.ccall('Z3_qe_model_project', 'number', ['number', 'number', 'number', 'array', 'number'], [
                    c,
                    m,
                    bound.length,
                    intArrayToByteArr(bound),
                    body,
                ]);
            },
            qe_model_project_skolem: function (c, m, bound, body, map) {
                return Mod.ccall('Z3_qe_model_project_skolem', 'number', ['number', 'number', 'number', 'array', 'number', 'number'], [
                    c,
                    m,
                    bound.length,
                    intArrayToByteArr(bound),
                    body,
                    map,
                ]);
            },
            model_extrapolate: Mod._Z3_model_extrapolate,
            qe_lite: Mod._Z3_qe_lite,
        },
    };
}
exports.init = init;

},{}]},{},[1])(1)
});
