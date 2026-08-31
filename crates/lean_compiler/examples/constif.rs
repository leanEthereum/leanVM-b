//! Temporary review driver: compile (and optionally execute) a zkDSL file.
use std::panic;

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args.next().expect("usage: constif <file.py> [run]");
    let run = args.next().as_deref() == Some("run");
    let src = std::fs::read_to_string(&path).expect("read");
    panic::set_hook(Box::new(|_| {}));
    let ast = match lean_compiler::parse(&src) {
        Ok(a) => a,
        Err(e) => {
            println!("PARSE-ERR: {e}");
            return;
        }
    };
    let prog = match panic::catch_unwind(|| lean_compiler::compile(&ast)) {
        Ok(p) => p,
        Err(e) => {
            let msg = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "<non-string panic>".into());
            println!("COMPILE-ERR: {msg}");
            return;
        }
    };
    println!("COMPILED: {} instructions", prog.prog.len());
    if run {
        let pi = [primitives::field::F192::ZERO; 2];
        match panic::catch_unwind(|| {
            prog.execute(pi).cycles
        }) {
            Ok(c) => println!("RAN: {c} cycles"),
            Err(e) => {
                let msg = e
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|| "<non-string panic>".into());
                println!("RUN-ERR: {msg}");
            }
        }
    }
}
