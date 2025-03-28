const env = {
    stack: [],
    error: void 0,
    hasError: false
};
try {
    var x = _ts_add_disposable_resource(env, A, false);
    var y = _ts_add_disposable_resource(env, B, true);
} catch (e) {
    env.error = e;
    env.hasError = true;
} finally{
    const result = _ts_dispose_resources(env);
    if (result) await result;
}
export { x, y };
