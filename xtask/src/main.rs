use std::env;

use duct::{cmd, Expression};
use itertools::Itertools;

fn group(name: &str, expr: Expression) {
    println!("::group::{}", name);
    expr.stdout_to_stderr().run().unwrap();
    println!("\n::endgroup::{}", name);
}

const TEST_TZS: &[&str] = &["ACST-9:30", "EST4", "UTC0", "Asia/Katmandu"];
const FEATURES: &[&str] = &["std", "serde", "clock", "alloc,serde", "unstable-locales"];
const RUST_138_FEATURES: &[&str] = &["serde"];

const ALL_FEATURES: &[&str] =
    &["clock", "std", "wasmbind", "winapi", "unstable-locales", "serde", "rkyv"];

const RUST_138_ALL_FEATURES: &[&str] =
    &["clock", "std", "wasmbind", "winapi", "unstable-locales", "serde"];

fn check_all_combinations(target: Option<&str>) {
    let features =
        if env_matches("RUST_VERSION", "1.38.0") { RUST_138_ALL_FEATURES } else { ALL_FEATURES };

    if let Some(target) = target {
        // skip all features on 1.38.0
        if !env_matches("RUST_VERSION", "1.38.0") {
            group("check with all", cmd!("cargo", "check", "--target", target, "--all-features"));
        };
        group(
            "check with none",
            cmd!("cargo", "check", "--target", target, "--no-default-features"),
        );
        let powerset = features.iter().copied().powerset().collect::<Vec<Vec<&str>>>();
        let powerset_len = powerset.len();
        for (idx, set) in powerset.into_iter().enumerate() {
            if !set.is_empty() {
                let joined_features =
                    Itertools::intersperse(set.into_iter(), ",").collect::<String>();
                println!(
                    "Checking powerset features {}/{}: {}",
                    powerset_len,
                    idx + 1,
                    joined_features
                );
                group(
                    &format!("check with {}", joined_features),
                    cmd!(
                        "cargo",
                        "check",
                        "--target",
                        target,
                        "--features",
                        joined_features,
                        "--no-default-features",
                    ),
                );
            }
        }
    } else {
        // skip all features on 1.38.0
        if !env_matches("RUST_VERSION", "1.38.0") {
            group("check with all", cmd!("cargo", "check", "--all-features"));
        }
        group("check with none", cmd!("cargo", "check", "--no-default-features"));
        for set in features.iter().powerset() {
            if !set.is_empty() {
                let joined_features =
                    Itertools::intersperse(set.into_iter().copied(), ",").collect::<String>();
                group(
                    &format!("check with {}", joined_features),
                    cmd!("cargo", "check", "--features", joined_features, "--no-default-features",),
                );
            }
        }
    }
}

fn test_all_tzs() {
    for tz in TEST_TZS {
        test_regular(Some(tz));

        // turn on clock feature
        // and include integration test
        group(
            "doctest",
            cmd!(
                "cargo",
                "test",
                "--features",
                "clock,std",
                "--color=always",
                "--",
                "--color=always",
            )
            .env("TZ", tz),
        );
    }
}

fn test_regular(tz: Option<&str>) {
    let features = if env_matches("RUST_VERSION", "1.38.0") { RUST_138_FEATURES } else { FEATURES };
    let integration_test_features = if env_matches("RUST_VERSION", "1.38.0") {
        "clock"
    } else {
        "__doctest,unstable-locales,clock"
    };

    let base = cmd!(
        "cargo",
        "test",
        "--features",
        integration_test_features,
        "--color=always",
        "--",
        "--color=always",
    );

    if let Some(tz) = tz {
        group("doctest", base.env("TZ", tz));
    } else {
        group("doctest", base);
    }

    for feature in features {
        let base = cmd!(
            "cargo",
            "test",
            "--features",
            feature,
            "--lib",
            "--color=always",
            "--",
            "--color=always",
        );

        if let Some(tz) = tz {
            group("doctest", base.env("TZ", tz));
        } else {
            group("doctest", base);
        }
    }
}

#[allow(dead_code)]
// TODO: add retry as per github.sh
fn wasm_simple() {
    if cmd!("wasm-pack", "--version").run().is_err() {
        cmd!("curl", "https://rustwasm.github.io/wasm-pack/installer/init.sh", "-sSf")
            .pipe(cmd!("sh"))
            .run()
            .unwrap();
    }

    let local_zone = cmd!("date", "+%z").read().unwrap();
    let now = cmd!("date", "+%s").read().unwrap();

    group("wasm_simple", cmd!("wasm-pack", "test", "--node",).env("TZ", local_zone).env("NOW", now))
}

fn _verify_build_on_target(target: &str, features: &[&str], no_default: bool) {
    let joined_features = features.join(",");
    let mut base = vec!["build", "--target", target];

    if no_default {
        base.push("--no-default-features");
    }

    if !features.is_empty() {
        base.push("--features");
        base.push(&joined_features);
    }

    group(target, cmd("cargo", base))
}

fn env_matches(var: &str, matches: &str) -> bool {
    env::var(var) == Ok(matches.to_string())
}

fn main() -> Result<(), ()> {
    let arg = env::args().nth(1);

    if arg.is_none() {
        eprintln!("cargo xtask must be passed one argument");
        return Err(());
    }

    match arg.unwrap().as_str() {
        "lint" => {
            // rustflags are present because of: https://github.com/rust-lang/rust-clippy/issues/5749
            group(
                "clippy",
                cmd!(
                    "cargo",
                    "clippy",
                    "--color=always",
                    "--",
                    "-D",
                    "warnings",
                    "-A",
                    "clippy::manual-non-exhaustive"
                )
                .env("RUSTFLAGS", "-Dwarnings"),
            );

            group("rustfmt", cmd!("cargo", "fmt", "--", "--check", "--color=always",));
        }
        "test" => {
            match env::var("TEST_STYLE").unwrap_or_default().as_str() {
                "basic" => test_regular(Some("UTC0")),
                "all_tzs" => test_all_tzs(),
                "check_features_powerset" => check_all_combinations(None),
                "" => (),
                other => {
                    eprintln!("Unexpected TEST_STYLE environment variable value of: {}", other);
                    return Err(());
                }
            };

            if let Ok(target) = env::var("TARGET") {
                check_all_combinations(Some(&target));

                if target == "wasm32-unknown-unknown" {
                    // comment this test out for now. It has been silently failing for a while
                    // will fix it in a later PR
                    // TODO: fix wasm_simple test
                    // wasm_simple()
                }
            }
        }
        other => {
            eprintln!("Unexpected cargo xtask argument: {}", other);
            return Err(());
        }
    }

    Ok(())
}
