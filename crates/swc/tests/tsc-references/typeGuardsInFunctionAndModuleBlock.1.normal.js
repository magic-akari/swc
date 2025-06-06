//// [typeGuardsInFunctionAndModuleBlock.ts]
// typeguards are scoped in function/module block
function foo(x) {
    return typeof x === "string" ? x : function f() {
        var b = x; // number | boolean
        return typeof x === "boolean" ? x.toString() // boolean
         : x.toString(); // number
    }();
}
function foo2(x) {
    return typeof x === "string" ? x : function f(a) {
        var b = x; // new scope - number | boolean
        return typeof x === "boolean" ? x.toString() // boolean
         : x.toString(); // number
    }(x); // x here is narrowed to number | boolean
}
function foo3(x) {
    return typeof x === "string" ? x : function() {
        var b = x; // new scope - number | boolean
        return typeof x === "boolean" ? x.toString() // boolean
         : x.toString(); // number
    }();
}
function foo4(x) {
    return typeof x === "string" ? x : function(a) {
        var b = x; // new scope - number | boolean
        return typeof x === "boolean" ? x.toString() // boolean
         : x.toString(); // number
    }(x); // x here is narrowed to number | boolean
}
// Type guards do not affect nested function declarations
function foo5(x) {
    if (typeof x === "string") {
        var foo = function foo() {
            var z = x; // string
        };
        var y = x; // string;
    }
}
(function(m) {
    var x;
    (function(m2) {
        var b = x; // new scope - number | boolean | string
        var y;
        if (typeof x === "string") {
            y = x; // string;
        } else {
            y = typeof x === "boolean" ? x.toString() // boolean
             : x.toString(); // number
        }
    })(m2 || (m2 = {}));
    var m2;
})(m || (m = {}));
(function(m1) {
    var x;
    (function(m2) {
        (function(m3) {
            var b = x; // new scope - number | boolean | string
            var y;
            if (typeof x === "string") {
                y = x; // string;
            } else {
                y = typeof x === "boolean" ? x.toString() // boolean
                 : x.toString(); // number
            }
        })(m2.m3 || (m2.m3 = {}));
    })(m2 || (m2 = {}));
    var m2;
})(m1 || (m1 = {}));
var m, m1;
