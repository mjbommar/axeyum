/* Axeyum render strand -- inlined page script.
 *
 * Rules this file lives by:
 *   - Every feature is optional. The document is fully readable with this
 *     script removed: detail blocks are <details>, the graph is static SVG,
 *     plot tooltips are native <title>, and the reading level defaults to
 *     "full" via a body attribute the emitter writes.
 *   - Nothing here may reach the network. No fetch, no XHR, no dynamic
 *     import, no new Image(). lint_self_contained() rejects those tokens.
 *   - Each feature is installed inside its own try/catch so one failure
 *     cannot take the others down.
 */
(function () {
  "use strict";

  function guard(name, fn) {
    try { fn(); } catch (e) {
      if (window.console && console.warn) { console.warn("axeyum: " + name + " disabled: " + e); }
    }
  }

  var $ = function (sel, root) { return (root || document).querySelector(sel); };
  var $$ = function (sel, root) {
    return Array.prototype.slice.call((root || document).querySelectorAll(sel));
  };

  /* -------- 1. reading level: summary / full / forensic -------- */
  guard("reading-level", function () {
    var group = $(".ax-levels");
    if (!group) { return; }
    var buttons = $$("button[data-level]", group);
    function apply(level) {
      document.body.setAttribute("data-level", level);
      buttons.forEach(function (b) {
        b.setAttribute("aria-pressed", b.getAttribute("data-level") === level ? "true" : "false");
      });
      // Forensic means "show me everything", so folds open; leaving the other
      // levels alone preserves whatever the reader opened by hand.
      if (level === "forensic") {
        $$("details.ax-fold").forEach(function (d) { d.open = true; });
      }
    }
    buttons.forEach(function (b) {
      b.addEventListener("click", function () { apply(b.getAttribute("data-level")); });
    });
    apply(document.body.getAttribute("data-level") || "full");
  });

  /* -------- 2. copy-to-clipboard for replay commands -------- */
  guard("copy", function () {
    $$("button[data-copy-target]").forEach(function (btn) {
      btn.addEventListener("click", function () {
        var src = document.getElementById(btn.getAttribute("data-copy-target"));
        if (!src) { return; }
        var text = src.textContent;
        var done = function (ok) {
          btn.setAttribute("data-copied", ok ? "1" : "0");
          var was = btn.getAttribute("data-label") || btn.textContent;
          btn.setAttribute("data-label", was);
          btn.textContent = ok ? "copied" : "select it";
          window.setTimeout(function () {
            btn.textContent = was;
            btn.removeAttribute("data-copied");
          }, 1400);
        };
        if (navigator.clipboard && navigator.clipboard.writeText) {
          navigator.clipboard.writeText(text).then(function () { done(true); }, function () { done(false); });
        } else {
          // Older engines: select the text so the reader can copy it manually.
          var r = document.createRange();
          r.selectNodeContents(src);
          var sel = window.getSelection();
          sel.removeAllRanges();
          sel.addRange(r);
          done(false);
        }
      });
    });
  });

  /* -------- 3. dependency graph: ancestor/descendant cone -------- */
  guard("graph-cone", function () {
    $$("svg.ax-graph").forEach(function (svg) {
      var nodes = $$("g.gnode", svg);
      var edges = $$("path.gedge", svg);
      function clear() {
        svg.classList.remove("coning");
        nodes.forEach(function (n) { n.classList.remove("cone-self", "cone-anc", "cone-desc"); });
        edges.forEach(function (e) { e.classList.remove("cone-edge"); });
      }
      function ids(el, attr) {
        var v = el.getAttribute(attr);
        return v ? v.split(" ") : [];
      }
      function light(node) {
        clear();
        var self = node.getAttribute("data-n");
        var anc = ids(node, "data-anc");
        var desc = ids(node, "data-desc");
        var inCone = {};
        inCone[self] = "self";
        anc.forEach(function (i) { inCone[i] = "anc"; });
        desc.forEach(function (i) { inCone[i] = "desc"; });
        nodes.forEach(function (n) {
          var k = inCone[n.getAttribute("data-n")];
          if (k) { n.classList.add("cone-" + k); }
        });
        edges.forEach(function (e) {
          var a = e.getAttribute("data-from"), b = e.getAttribute("data-to");
          if (inCone[a] && inCone[b]) { e.classList.add("cone-edge"); }
        });
        svg.classList.add("coning");
      }
      nodes.forEach(function (n) {
        n.addEventListener("mouseenter", function () { light(n); });
        n.addEventListener("focus", function () { light(n); });
        n.addEventListener("blur", clear);
        n.addEventListener("click", function () {
          var href = n.getAttribute("data-href");
          if (!href) { return; }
          var target = document.getElementById(href);
          if (target) {
            target.scrollIntoView({ block: "start", behavior: "smooth" });
            target.setAttribute("tabindex", "-1");
            target.focus({ preventScroll: true });
          }
        });
        n.addEventListener("keydown", function (ev) {
          if (ev.key === "Enter" || ev.key === " ") { ev.preventDefault(); n.dispatchEvent(new Event("click")); }
        });
      });
      svg.addEventListener("mouseleave", clear);
    });
  });

  /* -------- 4. steps player: j / k walk the derivation -------- */
  guard("steps", function () {
    $$("ol.ax-steps").forEach(function (list) {
      var items = $$("li", list);
      if (!items.length) { return; }
      var cur = -1;
      function show(i, scroll) {
        if (i < 0) { i = 0; }
        if (i >= items.length) { i = items.length - 1; }
        if (i === cur) { return; }
        if (cur >= 0) { items[cur].removeAttribute("aria-current"); }
        cur = i;
        items[cur].setAttribute("aria-current", "step");
        items[cur].setAttribute("tabindex", "0");
        if (scroll) { items[cur].scrollIntoView({ block: "nearest" }); }
      }
      items.forEach(function (li, i) {
        li.addEventListener("click", function () { show(i, false); });
      });
      list.setAttribute("tabindex", "0");
      list.addEventListener("keydown", function (ev) {
        var k = ev.key;
        if (k === "j" || k === "ArrowDown") { show(cur + 1, true); ev.preventDefault(); }
        else if (k === "k" || k === "ArrowUp") { show(cur < 0 ? 0 : cur - 1, true); ev.preventDefault(); }
        else if (k === "Home") { show(0, true); ev.preventDefault(); }
        else if (k === "End") { show(items.length - 1, true); ev.preventDefault(); }
      });
      var bar = list.previousElementSibling;
      if (bar && bar.classList.contains("ax-stepbar")) {
        var prev = $("button[data-step='prev']", bar);
        var next = $("button[data-step='next']", bar);
        if (prev) { prev.addEventListener("click", function () { show(cur < 0 ? 0 : cur - 1, true); }); }
        if (next) { next.addEventListener("click", function () { show(cur + 1, true); }); }
      }
    });
  });
})();
