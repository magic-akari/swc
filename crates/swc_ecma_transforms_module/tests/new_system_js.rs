#![deny(warnings)]

use std::path::PathBuf;

use swc_common::{chain, Mark};
use swc_ecma_parser::Syntax;
use swc_ecma_transforms_base::resolver;
use swc_ecma_transforms_module::new_system_js::{system_js, Config};
use swc_ecma_transforms_testing::{test_fixture, Tester};
use swc_ecma_visit::Fold;

fn syntax() -> Syntax {
    Syntax::Es(Default::default())
}

fn tr(_tester: &mut Tester<'_>, config: Config) -> impl Fold {
    let unresolved_mark = Mark::new();
    let top_level_mark = Mark::new();

    chain!(
        resolver(unresolved_mark, top_level_mark, false),
        system_js(unresolved_mark, config)
    )
}

#[testing::fixture("tests/fixture/systemjs/**/input.mjs")]
fn new_system_js(input: PathBuf) {
    let dir = input.parent().unwrap().to_path_buf();

    let output = dir.join("output.mjs");

    test_fixture(
        syntax(),
        &|tester| tr(tester, Default::default()),
        &input,
        &output,
        Default::default(),
    );
}
