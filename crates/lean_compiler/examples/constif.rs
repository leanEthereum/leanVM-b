//! Temporary review driver: compile, execute, and optionally prove/verify a zkDSL file.
use std::panic;

fn msg(e: Box<dyn std::any::Any + Send>) -> String {
    e.downcast_ref::<String>()
        .cloned()
        .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "<non-string panic>".into())
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args.next().expect("usage: constif <file.py> [run|prove <p0> <p1>]");
    let mode = args.next().unwrap_or_default();
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
            println!("COMPILE-ERR: {}", msg(e));
            return;
        }
    };
    println!("COMPILED: {} instructions", prog.prog.len());
    if mode.is_empty() {
        return;
    }
    let want: Vec<u64> = args.map(|a| a.parse().expect("u64")).collect();
    let pi = [
        primitives::field::F192::new(*want.first().unwrap_or(&0), 0, 0),
        primitives::field::F192::new(*want.get(1).unwrap_or(&0), 0, 0),
    ];
    match panic::catch_unwind(|| prog.execute(pi).cycles) {
        Ok(c) => println!("RAN: {c} cycles"),
        Err(e) => {
            println!("RUN-ERR: {}", msg(e));
            return;
        }
    }
    if mode == "prove" {
        let r = panic::catch_unwind(|| {
            let (proof, _) = lean_vm::cpu::prove(&prog, pi, lean_vm::pcs::LOG_INV_RATE);
            lean_vm::cpu::verify(&prog, &pi, &proof).is_ok()
        });
        match r {
            Ok(true) => println!("PROVED and VERIFIED"),
            Ok(false) => println!("VERIFY FAILED"),
            Err(e) => println!("PROVE-ERR: {}", msg(e)),
        }
    }
}
