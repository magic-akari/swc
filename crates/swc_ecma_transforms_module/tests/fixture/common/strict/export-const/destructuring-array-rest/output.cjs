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
    get bar () {
        return bar;
    },
    get baz () {
        return baz;
    },
    get foo () {
        return foo;
    }
});
const [foo, bar, ...baz] = [];
