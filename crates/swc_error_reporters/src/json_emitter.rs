use std::fmt::Write;

use serde_derive::Serialize;
use swc_common::{
    errors::{DiagnosticBuilder, DiagnosticId, Emitter},
    sync::Lrc,
    SourceMap, SourceMapper,
};

use crate::WriterWrapper;

pub struct JsonEmitter {
    cm: Lrc<SourceMap>,

    wr: WriterWrapper,

    config: JsonEmitterConfig,

    diagnostics: Vec<String>,
}

impl JsonEmitter {
    pub fn new(
        cm: Lrc<SourceMap>,
        wr: Box<dyn Write + Send + Sync>,
        config: JsonEmitterConfig,
    ) -> Self {
        Self {
            cm,
            wr: WriterWrapper(wr),
            config,
            diagnostics: vec![],
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct JsonEmitterConfig {
    pub skip_filename: bool,
}

impl Emitter for JsonEmitter {
    fn emit(&mut self, db: &DiagnosticBuilder) {
        let d = &**db;

        let children = d
            .children
            .iter()
            .map(|d| todo!("json subdiagnostic: {d:?}"))
            .collect::<Vec<_>>();

        let error_code = match &d.code {
            Some(DiagnosticId::Error(s)) => Some(&**s),
            Some(DiagnosticId::Lint(s)) => Some(&**s),
            None => None,
        };

        let loc = d
            .span
            .primary_span()
            .and_then(|span| self.cm.try_lookup_char_pos(span.lo()).ok());

        let snippet = d
            .span
            .primary_span()
            .and_then(|span| self.cm.span_to_snippet(span).ok());

        let filename = if self.config.skip_filename {
            None
        } else {
            loc.as_ref().map(|loc| loc.file.name.to_string())
        };

        let error = JsonDiagnostic {
            code: error_code,
            message: &d.message[0].0,
            snippet: snippet.as_deref(),
            filename: filename.as_deref(),
            line: loc.as_ref().map(|loc| loc.line),
            column: loc.as_ref().map(|loc| loc.col_display),
            children,
        };

        let result = serde_json::to_string(&error).unwrap();

        self.wr.write_str(&result).unwrap();
        writeln!(self.wr).unwrap();

        self.diagnostics.push(result);
    }

    fn take_diagnostics(&mut self) -> Vec<String> {
        std::mem::take(&mut self.diagnostics)
    }
}

#[derive(Serialize)]
struct JsonDiagnostic<'a> {
    /// Error code
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<&'a str>,
    message: &'a str,

    #[serde(skip_serializing_if = "Option::is_none")]
    snippet: Option<&'a str>,

    #[serde(skip_serializing_if = "Option::is_none")]
    filename: Option<&'a str>,

    #[serde(skip_serializing_if = "Option::is_none")]
    line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    column: Option<usize>,

    #[serde(skip_serializing_if = "Vec::is_empty")]
    children: Vec<JsonSubdiagnostic<'a>>,
}

#[derive(Serialize)]
struct JsonSubdiagnostic<'a> {
    message: &'a str,
    snippet: Option<&'a str>,
    filename: &'a str,
    line: usize,
}
