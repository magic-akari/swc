const Z = (f)=>((x)=>f((y)=>x(x)(y)))((x)=>f((y)=>x(x)(y)));
const p = Z((f)=>(n = 0)=>_async_to_generator(function*() {
            return n <= 1 ? 1 : n * (yield f(n - 1));
        })())(5);
