const chronoFactory = require("./chrono");
const assert = require("assert");

chronoFactory().then((chronoRaw) => {
  const chrono = {
    currentTimeUtc: chronoRaw.cwrap("current_time_utc", "string", []),
    currentTimeLocal: chronoRaw.cwrap("current_time_local", "string", []),
    timezoneOffset: chronoRaw.cwrap("timezone_offset", "number", []),
  };
  const currentTimeJs = new Date().getTime();

  console.log(`Current time (Wasm: UTC): ${chrono.currentTimeUtc()}`);
  console.log(`Current time (Wasm: Local): ${chrono.currentTimeLocal()}`);
  console.log(`Current time (JS): ${new Date(currentTimeJs).toISOString()}`);
  const currentTimeUtcParsed = Date.parse(chrono.currentTimeUtc());
  const currentTimeLocalParsed = Date.parse(chrono.currentTimeLocal());

  const diffUtc = Math.abs(currentTimeUtcParsed - currentTimeJs);
  const diffLocal = Math.abs(currentTimeLocalParsed - currentTimeJs);
  console.log("")
  console.log("Test #1: The difference should be less than 1 second:")
  console.log(`Difference (UTC): ${diffUtc} ms`);
  console.log(`Difference (Local): ${diffLocal} ms`);
  assert(diffUtc < 1000);
  assert(diffLocal < 1000);

  console.log("")
  console.log("Test #2: Timezone offset should be the same:")
  const timezoneJs = new Date().getTimezoneOffset();
  const timezoneWasm = chrono.timezoneOffset();
  console.log(`Timezone (JS): ${timezoneJs} min`);
  console.log(`Timezone (Wasm): ${timezoneWasm} sec (${timezoneWasm / 60} min)`);
  assert(timezoneJs === timezoneWasm / 60);

  console.log("");
  console.log("All tests passed.");
});
