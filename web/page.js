const inp = document.querySelector("#input");

//       var s = `effect Eff : unit

// let test ()
// (*@ ex i ;
//   Eff(i->0, ret);
//   req i-> z;
//   Norm(i->z+1, ret)
// @*)
// =
//   let i = Sys.opaque_identity (ref 0) in
//   let ret = perform Eff in
//   i := !i + 1;
//   ret`;

// inp.value = s;

function run() {
  clear_output();
  hip_run_string(false, inp.value);
}
function enable_buttons() {
  document.querySelector("#run-btn").disabled = false;
  document.querySelector("#share-btn").disabled = false;
}
function load_example(s) {
  clear_output();
  inp.value = s.value;
}

const field = document.querySelector("#output");
const old_console = console;

const redirect_output = true;
if (redirect_output) {
  window.console = {
    log(...args) {
      // field.value += args.join(' ') + '\n';
      field.innerHTML +=
        '<div class="output-line">' +
        args.join(" ").replace(/\n/g, '</div><div class="output-line">') +
        "</div>";
      // field.textContent += args.join(" ");
      // old_console.log(...args);
    },
  };
}

function clear_output() {
  field.innerHTML = "";
}

function share() {
  const url = new URL(window.location);
  url.search = new URLSearchParams({ c: window.btoa(inp.value) });
  // this navigates away
  // window.location = url.toString();
  history.pushState({}, "Shared URL", url.toString());
}

const queryParams = new URLSearchParams(window.location.search);
if (queryParams.get("c") !== null) {
  const code = window.atob(queryParams.get("c"));
  inp.value = code;
} else {
  load_example(document.querySelector("#examples"));
}
