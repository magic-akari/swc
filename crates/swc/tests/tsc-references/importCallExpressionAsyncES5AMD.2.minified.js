//// [test.ts]
define([
    "require",
    "exports",
    "@swc/helpers/_/_async_to_generator",
    "@swc/helpers/_/_class_call_check",
    "@swc/helpers/_/_interop_require_wildcard",
    "@swc/helpers/_/_ts_generator"
], function(require, exports, _async_to_generator, _class_call_check, _interop_require_wildcard, _ts_generator) {
    Object.defineProperty(exports, "__esModule", {
        value: !0
    });
    var all = {
        get cl1 () {
            return cl1;
        },
        get cl2 () {
            return cl2;
        },
        get fn () {
            return fn;
        },
        get l () {
            return l;
        },
        get obj () {
            return obj;
        }
    };
    for(var name in all)Object.defineProperty(exports, name, {
        enumerable: !0,
        get: Object.getOwnPropertyDescriptor(all, name).get
    });
    function fn() {
        return _async_to_generator._(function() {
            return _ts_generator._(this, function(_state) {
                switch(_state.label){
                    case 0:
                        return [
                            4,
                            new Promise(function(resolve, reject) {
                                return require([
                                    "./test"
                                ], function(m) {
                                    return resolve(/*#__PURE__*/ _interop_require_wildcard._(m));
                                }, reject);
                            })
                        ];
                    case 1:
                        return _state.sent(), [
                            2
                        ];
                }
            });
        })();
    }
    var cl1 = /*#__PURE__*/ function() {
        function cl1() {
            _class_call_check._(this, cl1);
        }
        return cl1.prototype.m = function() {
            return _async_to_generator._(function() {
                return _ts_generator._(this, function(_state) {
                    switch(_state.label){
                        case 0:
                            return [
                                4,
                                new Promise(function(resolve, reject) {
                                    return require([
                                        "./test"
                                    ], function(m) {
                                        return resolve(/*#__PURE__*/ _interop_require_wildcard._(m));
                                    }, reject);
                                })
                            ];
                        case 1:
                            return _state.sent(), [
                                2
                            ];
                    }
                });
            })();
        }, cl1;
    }(), obj = {
        m: function() {
            return _async_to_generator._(function() {
                return _ts_generator._(this, function(_state) {
                    switch(_state.label){
                        case 0:
                            return [
                                4,
                                new Promise(function(resolve, reject) {
                                    return require([
                                        "./test"
                                    ], function(m) {
                                        return resolve(/*#__PURE__*/ _interop_require_wildcard._(m));
                                    }, reject);
                                })
                            ];
                        case 1:
                            return _state.sent(), [
                                2
                            ];
                    }
                });
            })();
        }
    }, cl2 = function cl2() {
        _class_call_check._(this, cl2), this.p = {
            m: function() {
                return _async_to_generator._(function() {
                    return _ts_generator._(this, function(_state) {
                        switch(_state.label){
                            case 0:
                                return [
                                    4,
                                    new Promise(function(resolve, reject) {
                                        return require([
                                            "./test"
                                        ], function(m) {
                                            return resolve(/*#__PURE__*/ _interop_require_wildcard._(m));
                                        }, reject);
                                    })
                                ];
                            case 1:
                                return _state.sent(), [
                                    2
                                ];
                        }
                    });
                })();
            }
        };
    }, l = function() {
        return _async_to_generator._(function() {
            return _ts_generator._(this, function(_state) {
                switch(_state.label){
                    case 0:
                        return [
                            4,
                            new Promise(function(resolve, reject) {
                                return require([
                                    "./test"
                                ], function(m) {
                                    return resolve(/*#__PURE__*/ _interop_require_wildcard._(m));
                                }, reject);
                            })
                        ];
                    case 1:
                        return _state.sent(), [
                            2
                        ];
                }
            });
        })();
    };
});
