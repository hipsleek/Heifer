function run() {
  clear_output();
  hip_run_string(false, editorGet());
}
function enable_buttons() {
  document.querySelector("#run-btn").disabled = false;
  document.querySelector("#share-btn").disabled = false;
}
function load_example(s) {
  clear_output();
  editorSet(s.value);
}

// const inp = document.querySelector("#input");
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
  url.search = new URLSearchParams({ c: window.btoa(editorGet()) });
  // this navigates away
  // window.location = url.toString();
  history.pushState({}, "Shared URL", url.toString());
}

let editor;
function setupEditor() {
  editor = ace.edit("editor");
  editor.setTheme("ace/theme/xcode");
  editor.setShowPrintMargin(false);
  editor.setHighlightActiveLine(false);
  editor.setOption("displayIndentGuides", false);
  editor.session.setUseWorker(false);
  editor.session.setUseWrapMode(true);
  editor.session.setOptions({
    mode: "ace/mode/ocaml",
    tabSize: 2,
    useSoftTabs: true,
    fontSize: "14pt",
  });
  editor.commands.addCommand({
    name: "Run",
    bindKey: { win: "Ctrl-Enter", mac: "Command-Enter" },
    exec: function (_editor) {
      run();
    },
    // scrollIntoView: "cursor",
  });
  editor.focus();
}

function editorSet(s) {
  // inp.value = s;
  editor.setValue(s, -1);
}

function editorGet(s) {
  // return inp.value;
  return editor.getValue();
}

function vim() {
  editor.setKeyboardHandler("ace/keyboard/vim");
}

function main() {
  const queryParams = new URLSearchParams(window.location.search);
  if (queryParams.get("c") !== null) {
    const code = window.atob(queryParams.get("c"));
    editorSet(code);
  } else {
    load_example(document.querySelector("#examples"));
  }
}

setupEditor();
main();
