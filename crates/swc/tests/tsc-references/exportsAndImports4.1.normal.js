//// [exportsAndImports4.ts]
"use strict";
//// [t1.ts]
"use strict";
Object.defineProperty(exports, "__esModule", {
    value: true
});
Object.defineProperty(exports, "default", {
    enumerable: true,
    get: function() {
        return _default;
    }
});
var _default = "hello";
//// [t2.ts]
"use strict";
Object.defineProperty(exports, "__esModule", {
    value: true
});
var _interop_require_wildcard = require("@swc/helpers/_/_interop_require_wildcard");
var _t1 = /*#__PURE__*/ _interop_require_wildcard._(require("./t1"));
var a = require("./t1");
a.default;
_t1.default;
_t1.default;
_t1.default;
_t1.default;
_t1.default;
_t1.default;
_t1.default;
//// [t3.ts]
"use strict";
Object.defineProperty(exports, "__esModule", {
    value: true
});
function _export(target, all) {
    for(var name in all)Object.defineProperty(target, name, {
        enumerable: true,
        get: Object.getOwnPropertyDescriptor(all, name).get
    });
}
_export(exports, {
    get a () {
        return a;
    },
    get b () {
        return _t1.default;
    },
    get c () {
        return _t1;
    },
    get d () {
        return _t1.default;
    },
    get e1 () {
        return _t1.default;
    },
    get e2 () {
        return _t1;
    },
    get f1 () {
        return _t1.default;
    },
    get f2 () {
        return _t1.default;
    }
});
var _interop_require_wildcard = require("@swc/helpers/_/_interop_require_wildcard");
var _t1 = /*#__PURE__*/ _interop_require_wildcard._(require("./t1"));
var a = require("./t1");
a.default;
_t1.default;
_t1.default;
_t1.default;
_t1.default;
_t1.default;
_t1.default;
_t1.default;
