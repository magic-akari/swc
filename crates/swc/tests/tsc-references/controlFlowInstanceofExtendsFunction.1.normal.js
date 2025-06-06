//// [controlFlowInstanceofExtendsFunction.ts]
import { _ as _class_call_check } from "@swc/helpers/_/_class_call_check";
import { _ as _instanceof } from "@swc/helpers/_/_instanceof";
Function.prototype.now = function() {
    return "now";
};
var X = /*#__PURE__*/ function() {
    "use strict";
    function X() {
        _class_call_check(this, X);
    }
    var _proto = X.prototype;
    _proto.why = function why() {};
    X.now = function now() {
        return {};
    };
    return X;
}();
var Y = function Y() {
    "use strict";
    _class_call_check(this, Y);
};
console.log(X.now()); // works as expected
console.log(Y.now()); // works as expected
export var x = Math.random() > 0.5 ? new X() : 1;
if (_instanceof(x, X)) {
    x.why(); // should compile
}
