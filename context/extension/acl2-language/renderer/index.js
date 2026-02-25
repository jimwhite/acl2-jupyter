// ACL2 Events Renderer for VS Code Notebooks
// Renders application/vnd.acl2.events+json output

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Create an element with inline styles from an object. */
function el(tag, styles, textContent) {
  const e = document.createElement(tag);
  if (styles) Object.assign(e.style, styles);
  if (textContent !== undefined) e.textContent = textContent;
  return e;
}

/** Badge span used for package names, symbol kinds, etc. */
function badge(text, bg, fg) {
  return el("span", {
    display: "inline-block",
    padding: "1px 6px",
    borderRadius: "4px",
    backgroundColor: bg || "var(--vscode-badge-background, #4d4d4d)",
    color: fg || "var(--vscode-badge-foreground, #fff)",
    fontSize: "0.85em",
  }, text);
}

/** Muted description text. */
function muted(text) {
  return el("span", {
    fontSize: "0.85em",
    color: "var(--vscode-descriptionForeground, #888)",
  }, text);
}

/** A clickable toggle that shows/hides a target element. */
function makeToggle(label, target) {
  const btn = el("span", {
    cursor: "pointer",
    fontSize: "0.85em",
    color: "var(--vscode-textLink-foreground, #3794ff)",
    userSelect: "none",
  }, `▶ ${label}`);
  let open = false;
  btn.addEventListener("click", () => {
    open = !open;
    target.style.display = open ? "block" : "none";
    btn.textContent = open ? `▼ ${label}` : `▶ ${label}`;
  });
  return btn;
}

/** Card container for detail items. */
function card() {
  return el("div", {
    marginTop: "6px",
    padding: "6px 8px",
    borderRadius: "4px",
    backgroundColor: "var(--vscode-editor-background, #1e1e1e)",
    border: "1px solid var(--vscode-panel-border, #333)",
  });
}

/** Pre-formatted code block. */
function codeBlock(text) {
  return el("div", {
    whiteSpace: "pre-wrap",
    wordBreak: "break-word",
    color: "var(--vscode-editor-foreground, #d4d4d4)",
  }, text);
}

// Kind → badge colour mapping (VS Code theme-friendly)
const KIND_COLORS = {
  function:       ["var(--vscode-symbolIcon-functionForeground, #b180d7)", "var(--vscode-editor-background, #1e1e1e)"],
  macro:          ["var(--vscode-symbolIcon-enumeratorForeground, #ee9d28)", "var(--vscode-editor-background, #1e1e1e)"],
  theorem:        ["var(--vscode-symbolIcon-interfaceForeground, #75beff)", "var(--vscode-editor-background, #1e1e1e)"],
  constant:       ["var(--vscode-symbolIcon-constantForeground, #4fc1ff)", "var(--vscode-editor-background, #1e1e1e)"],
  stobj:          ["var(--vscode-symbolIcon-structForeground, #ee9d28)", "var(--vscode-editor-background, #1e1e1e)"],
  "special-form": ["var(--vscode-symbolIcon-keywordForeground, #c586c0)", "var(--vscode-editor-background, #1e1e1e)"],
  "cl-macro":     ["var(--vscode-symbolIcon-enumeratorMemberForeground, #ee9d28)", "var(--vscode-editor-background, #1e1e1e)"],
  "cl-function":  ["var(--vscode-symbolIcon-methodForeground, #b180d7)", "var(--vscode-editor-background, #1e1e1e)"],
  "cl-variable":  ["var(--vscode-symbolIcon-variableForeground, #75beff)", "var(--vscode-editor-background, #1e1e1e)"],
};

// ---------------------------------------------------------------------------
// Section builders
// ---------------------------------------------------------------------------

/** Build the Events / Forms section (existing feature). */
function buildEventsSection(events, forms) {
  const wrap = el("div", { display: "none", padding: "0 8px 4px" });
  const count = Math.max(events.length, forms.length);
  for (let i = 0; i < count; i++) {
    const c = card();
    if (i < forms.length && forms[i]) {
      c.appendChild(codeBlock(forms[i]));
    }
    if (i < events.length && events[i]) {
      const ev = codeBlock(events[i]);
      if (i < forms.length && forms[i]) {
        Object.assign(ev.style, {
          fontSize: "0.9em",
          marginTop: "4px",
          color: "var(--vscode-descriptionForeground, #888)",
        });
      }
      c.appendChild(ev);
    }
    wrap.appendChild(c);
  }
  return wrap;
}

/** Build the Symbols section — a compact table. */
function buildSymbolsSection(symbols) {
  const wrap = el("div", { display: "none", padding: "0 8px 4px" });
  const table = el("table", {
    width: "100%",
    borderCollapse: "collapse",
    marginTop: "4px",
    fontSize: "0.9em",
  });

  // Column config: header, width, align
  const cols = [
    { header: "Package", width: "15%", align: "right" },
    { header: "Name",    width: "60%", align: "left" },
    { header: "Kind",    width: "15%", align: "left" },
    { header: "Pos",     width: "10%", align: "left" },
  ];

  // Colgroup
  const colgroup = document.createElement("colgroup");
  for (const col of cols) {
    const c = document.createElement("col");
    c.style.width = col.width;
    colgroup.appendChild(c);
  }
  table.appendChild(colgroup);

  // Header
  const thead = document.createElement("thead");
  const hr = document.createElement("tr");
  for (const col of cols) {
    const th = el("th", {
      textAlign: col.align,
      padding: "2px 8px 2px 0",
      borderBottom: "1px solid var(--vscode-panel-border, #333)",
      color: "var(--vscode-descriptionForeground, #888)",
      fontWeight: "normal",
    }, col.header);
    hr.appendChild(th);
  }
  thead.appendChild(hr);
  table.appendChild(thead);

  // Rows
  const tbody = document.createElement("tbody");
  for (const sym of symbols) {
    const tr = document.createElement("tr");

    // Package (right-aligned)
    tr.appendChild(el("td", {
      padding: "2px 8px 2px 0",
      textAlign: "right",
      color: "var(--vscode-descriptionForeground, #888)",
    }, sym.package));

    // Name (left-aligned, widest)
    const tdName = el("td", { padding: "2px 8px 2px 0", textAlign: "left" });
    tdName.appendChild(el("code", {
      color: "var(--vscode-editor-foreground, #d4d4d4)",
    }, sym.name));
    tr.appendChild(tdName);

    // Kind badge (left-aligned)
    const tdKind = el("td", { padding: "2px 8px 2px 0", textAlign: "left" });
    const colors = KIND_COLORS[sym.kind] || [
      "var(--vscode-badge-background, #4d4d4d)",
      "var(--vscode-badge-foreground, #fff)",
    ];
    tdKind.appendChild(badge(sym.kind, colors[0], colors[1]));
    tr.appendChild(tdKind);

    // Position (left-aligned)
    const pos = [];
    if (sym.operator) pos.push("op");
    if (sym.argument) pos.push("arg");
    tr.appendChild(el("td", {
      padding: "2px 8px 2px 0",
      textAlign: "left",
      color: "var(--vscode-descriptionForeground, #888)",
      fontSize: "0.9em",
    }, pos.join(", ") || "—"));

    tbody.appendChild(tr);
  }
  table.appendChild(tbody);
  wrap.appendChild(table);
  return wrap;
}

/** Build the Dependencies section — definition → references. */
function buildDependenciesSection(dependencies) {
  const wrap = el("div", { display: "none", padding: "0 8px 4px" });
  const keys = Object.keys(dependencies);
  for (const defName of keys) {
    const refs = dependencies[defName];
    const c = card();

    // Defined name
    const header = el("div", { marginBottom: "4px" });
    header.appendChild(el("code", {
      color: "var(--vscode-symbolIcon-functionForeground, #b180d7)",
      fontWeight: "bold",
    }, defName));
    header.appendChild(muted(` → ${refs.length} ref${refs.length !== 1 ? "s" : ""}`));
    c.appendChild(header);

    // Reference list
    const refList = el("div", {
      display: "flex",
      flexWrap: "wrap",
      gap: "4px",
    });
    for (const ref of refs) {
      refList.appendChild(badge(ref,
        "var(--vscode-badge-background, #4d4d4d)",
        "var(--vscode-badge-foreground, #fff)"));
    }
    c.appendChild(refList);
    wrap.appendChild(c);
  }
  return wrap;
}

/** Build the Expansions section — form → expanded code. */
function buildExpansionsSection(expansions) {
  const wrap = el("div", { display: "none", padding: "0 8px 4px" });
  for (const exp of expansions) {
    const c = card();

    // Original form
    const formLabel = muted("form");
    formLabel.style.display = "block";
    formLabel.style.marginBottom = "2px";
    c.appendChild(formLabel);
    c.appendChild(codeBlock(exp.form));

    // Arrow
    c.appendChild(el("div", {
      textAlign: "center",
      color: "var(--vscode-descriptionForeground, #888)",
      margin: "4px 0",
    }, "↓ expands to"));

    // Expansion
    const expLabel = muted("expansion");
    expLabel.style.display = "block";
    expLabel.style.marginBottom = "2px";
    c.appendChild(expLabel);
    const expCode = codeBlock(exp.expansion);
    expCode.style.color = "var(--vscode-symbolIcon-functionForeground, #b180d7)";
    c.appendChild(expCode);

    wrap.appendChild(c);
  }
  return wrap;
}

/** Build the Raw Definitions section — list of symbols with CL-level changes. */
function buildRawDefsSection(rawDefs) {
  const wrap = el("div", { display: "none", padding: "0 8px 4px" });
  const c = card();
  const list = el("div", { display: "flex", flexWrap: "wrap", gap: "4px" });
  for (const name of rawDefs) {
    list.appendChild(badge(name,
      "var(--vscode-inputValidation-warningBackground, #352a05)",
      "var(--vscode-inputValidation-warningForeground, #cca700)"));
  }
  c.appendChild(list);
  wrap.appendChild(c);
  return wrap;
}

// ---------------------------------------------------------------------------
// Main Renderer
// ---------------------------------------------------------------------------

export const activate = (context) => ({
  renderOutputItem(data, element) {
    const acl2Data = data.json();
    const events = acl2Data.events || [];
    const forms = acl2Data.forms || [];
    const pkg = acl2Data.package || "ACL2";
    const symbols = acl2Data.symbols || [];
    const dependencies = acl2Data.dependencies || {};
    const expansions = acl2Data.expansions || [];
    const rawDefs = acl2Data.raw_definitions || [];

    const depCount = Object.keys(dependencies).length;
    const hasEvents = events.length > 0 || forms.length > 0;
    const hasExworld = symbols.length > 0 || depCount > 0 || expansions.length > 0 || rawDefs.length > 0;
    const hasContent = hasEvents || hasExworld;

    // Container
    const container = el("div", {
      fontFamily: "var(--vscode-editor-font-family, monospace)",
      fontSize: "var(--vscode-editor-font-size, 13px)",
      lineHeight: "1.5",
    });

    // Header row
    const headerRow = el("div", {
      display: "flex",
      alignItems: "center",
      gap: "6px",
      padding: hasContent ? "4px 8px" : "0px 8px",
      flexWrap: "wrap",
    });

    // Package badge
    headerRow.appendChild(badge(pkg));

    if (hasContent) {
      // Summary counts
      const parts = [];
      if (forms.length > 0) parts.push(`${forms.length} form${forms.length !== 1 ? "s" : ""}`);
      if (events.length > 0) parts.push(`${events.length} event${events.length !== 1 ? "s" : ""}`);
      if (symbols.length > 0) parts.push(`${symbols.length} sym`);
      if (depCount > 0) parts.push(`${depCount} dep${depCount !== 1 ? "s" : ""}`);
      if (expansions.length > 0) parts.push(`${expansions.length} exp`);
      if (rawDefs.length > 0) parts.push(`${rawDefs.length} raw`);
      headerRow.appendChild(muted(parts.join(" · ")));

      // Sections — each gets its own toggle + detail container
      const sections = [];

      if (hasEvents) {
        const sec = buildEventsSection(events, forms);
        const label = forms.length > 0 ? "Forms" : "Events";
        sections.push({ label, sec });
      }
      if (symbols.length > 0) {
        sections.push({ label: "Symbols", sec: buildSymbolsSection(symbols) });
      }
      if (depCount > 0) {
        sections.push({ label: "Deps", sec: buildDependenciesSection(dependencies) });
      }
      if (expansions.length > 0) {
        sections.push({ label: "Expand", sec: buildExpansionsSection(expansions) });
      }
      if (rawDefs.length > 0) {
        sections.push({ label: "Raw", sec: buildRawDefsSection(rawDefs) });
      }

      for (const { label, sec } of sections) {
        headerRow.appendChild(makeToggle(label, sec));
      }

      container.appendChild(headerRow);
      for (const { sec } of sections) {
        container.appendChild(sec);
      }
    } else {
      container.appendChild(headerRow);
    }

    element.innerHTML = "";
    element.appendChild(container);
  },

  disposeOutputItem(id) {
    // Nothing to clean up
  }
});
