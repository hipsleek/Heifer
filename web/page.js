function run() {
  clear_output();
  hip_run_string(false, editorGet());
}
function enable_buttons() {
  document.querySelector("#run-btn").disabled = false;
  document.querySelector("#share-btn").disabled = false;
}

const examples = document.querySelector("#examples");
function load_selected_example() {
  clear_output();
  editorSet(current_example_text());
}
function current_example_name() {
  return examples[examples.selectedIndex].value;
}
function current_example_text() {
  return examples[examples.selectedIndex].dataset.text.trim();
}

// const inp = document.querySelector("#input");
const field = document.querySelector("#output");
const debug = document.querySelector("#debug");
const old_console = console;

function debug_output() {
  return debug.checked;
}

function clear_output() {
  field.innerHTML = "";
}

function share() {
  if (editorGet().trim() === current_example_text()) {
    const url = new URL(window.location);
    url.search = new URLSearchParams({ example: current_example_name() });
    history.pushState({}, "Shared Example URL", url.toString());
  } else {
    const url = new URL(window.location);
    url.search = new URLSearchParams({ code: window.btoa(editorGet()) });
    // this navigates away
    // window.location = url.toString();
    history.pushState({}, "Shared Code URL", url.toString());
  }
}

let editor;
function setupEditor() {
  // https://ace.c9.io/tool/mode_creator.html
  // https://github.com/ajaxorg/ace/wiki/Creating-or-Extending-an-Edit-Mode

  ace.define("ace/mode/ocaml1", function (require, exports, module) {
    var oop = require("ace/lib/oop");
    var TextMode = require("ace/mode/text").Mode;
    var OcamlHighlightRules =
      require("ace/mode/ocaml1_highlight_rules").OcamlHighlightRules;

    var Mode = function () {
      this.HighlightRules = OcamlHighlightRules;
    };
    oop.inherits(Mode, TextMode);

    (function () {
      // Extra logic goes here. (see below)
    }).call(Mode.prototype);

    exports.Mode = Mode;
  });

  ace.define(
    "ace/mode/ocaml1_highlight_rules",
    function (require, exports, module) {
      var oop = require("ace/lib/oop");
      var TextHighlightRules =
        require("ace/mode/text_highlight_rules").TextHighlightRules;

      oop.inherits(OcamlHighlightRules, TextHighlightRules);

      exports.OcamlHighlightRules = OcamlHighlightRules;
    }
  );

  editor = ace.edit("editor");
  editor.setTheme("ace/theme/xcode");
  editor.setShowPrintMargin(false);
  editor.setHighlightActiveLine(false);
  editor.setOption("displayIndentGuides", false);
  editor.commands.bindKey("Cmd-L", null);
  editor.session.setUseWorker(false);
  editor.session.setUseWrapMode(true);
  editor.session.setOptions({
    mode: "ace/mode/ocaml1",
    tabSize: 2,
    useSoftTabs: true,
  });
  editor.setFontSize("12px");
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

function editorGet() {
  // return inp.value;
  return editor.getValue();
}

function vim() {
  editor.setKeyboardHandler("ace/keyboard/vim");
}

function main() {
  const queryParams = new URLSearchParams(window.location.search);
  if (queryParams.get("code") !== null) {
    const code = window.atob(queryParams.get("code"));
    editorSet(code);
  } else if (queryParams.get("example") !== null) {
    examples.value = queryParams.get("example");
    load_selected_example();
  } else {
    load_selected_example();
  }
  postExampleLoad();
}

setupEditor();
main();
