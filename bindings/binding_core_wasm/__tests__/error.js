const swc = require("../pkg");

it("properly reports error", () => {
    expect(() => {
        swc.transformSync("Foo {}", {});
    }).toThrow("Syntax Error");

    expect(() => {
        swc.transformSync("Foo {}", {});
    }).toThrow("Expected ';', '}' or <eof>");
});
