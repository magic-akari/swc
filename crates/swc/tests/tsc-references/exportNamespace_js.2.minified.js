//// [exportNamespace_js.ts]
//// [a.js]
import { _ as _class_call_check } from "@swc/helpers/_/_class_call_check";
export var A = function A() {
    _class_call_check(this, A);
};
//// [b.js]
export { };
//// [c.js]
import './b';
