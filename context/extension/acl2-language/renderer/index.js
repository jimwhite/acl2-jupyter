// ACL2 Events Renderer for VS Code Notebooks
// Renders application/vnd.acl2.events+json output

export const activate = (context) => ({
  renderOutputItem(data, element) {
    const acl2Data = data.json();
    const events = acl2Data.events || [];
    const forms = acl2Data.forms || [];
    const pkg = acl2Data.package || "ACL2";
    const hasContent = events.length > 0 || forms.length > 0;

    // Create container
    const container = document.createElement("div");
    container.style.fontFamily = "var(--vscode-editor-font-family, monospace)";
    container.style.fontSize = "var(--vscode-editor-font-size, 13px)";
    container.style.lineHeight = "1.5";

    // Header row: package + counts + toggle (all on one line)
    const headerRow = document.createElement("div");
    headerRow.style.display = "flex";
    headerRow.style.alignItems = "center";
    headerRow.style.gap = "6px";
    headerRow.style.padding = hasContent ? "4px 8px" : "0px 8px";

    // Package badge
    const pkgBadge = document.createElement("span");
    pkgBadge.style.display = "inline-block";
    pkgBadge.style.padding = "1px 6px";
    pkgBadge.style.borderRadius = "4px";
    pkgBadge.style.backgroundColor = "var(--vscode-badge-background, #4d4d4d)";
    pkgBadge.style.color = "var(--vscode-badge-foreground, #fff)";
    pkgBadge.style.fontSize = "0.85em";
    pkgBadge.textContent = pkg;
    headerRow.appendChild(pkgBadge);

    if (hasContent) {
      // Counts
      const countsEl = document.createElement("span");
      countsEl.style.fontSize = "0.85em";
      countsEl.style.color = "var(--vscode-descriptionForeground, #888)";
      const parts = [];
      if (forms.length > 0) parts.push(`${forms.length} form${forms.length !== 1 ? "s" : ""}`);
      if (events.length > 0) parts.push(`${events.length} event${events.length !== 1 ? "s" : ""}`);
      countsEl.textContent = parts.join(", ");
      headerRow.appendChild(countsEl);

      // Toggle button (right after counts)
      const toggleBtn = document.createElement("span");
      toggleBtn.style.cursor = "pointer";
      toggleBtn.style.fontSize = "0.85em";
      toggleBtn.style.color = "var(--vscode-textLink-foreground, #3794ff)";
      toggleBtn.style.userSelect = "none";
      toggleBtn.textContent = "▶ Show";
      headerRow.appendChild(toggleBtn);

      // Details container (hidden by default)
      const detailsDiv = document.createElement("div");
      detailsDiv.style.display = "none";
      detailsDiv.style.padding = "0 8px 4px";

      let expanded = false;
      toggleBtn.addEventListener("click", () => {
        expanded = !expanded;
        detailsDiv.style.display = expanded ? "block" : "none";
        toggleBtn.textContent = expanded ? "▼ Hide" : "▶ Show";
      });

      // Build event/form blocks
      const count = Math.max(events.length, forms.length);
      for (let i = 0; i < count; i++) {
        const eventBlock = document.createElement("div");
        eventBlock.style.marginTop = "6px";
        eventBlock.style.padding = "6px 8px";
        eventBlock.style.borderRadius = "4px";
        eventBlock.style.backgroundColor = "var(--vscode-editor-background, #1e1e1e)";
        eventBlock.style.border = "1px solid var(--vscode-panel-border, #333)";

        // Show form if present
        if (i < forms.length && forms[i]) {
          const formEl = document.createElement("div");
          formEl.style.color = "var(--vscode-editor-foreground, #d4d4d4)";
          formEl.style.whiteSpace = "pre-wrap";
          formEl.style.wordBreak = "break-word";
          formEl.textContent = forms[i];
          eventBlock.appendChild(formEl);
        }

        // Show event landmark
        if (i < events.length && events[i]) {
          const eventEl = document.createElement("div");
          eventEl.style.color = "var(--vscode-textPreformat-foreground, #ce9178)";
          eventEl.style.whiteSpace = "pre-wrap";
          eventEl.style.wordBreak = "break-word";
          if (i < forms.length && forms[i]) {
            eventEl.style.fontSize = "0.9em";
            eventEl.style.marginTop = "4px";
            eventEl.style.color = "var(--vscode-descriptionForeground, #888)";
          }
          eventEl.textContent = events[i];
          eventBlock.appendChild(eventEl);
        }

        detailsDiv.appendChild(eventBlock);
      }

      container.appendChild(headerRow);
      container.appendChild(detailsDiv);
    } else {
      // Zero events/forms: minimal footprint — just the header row with no padding
      container.appendChild(headerRow);
    }

    element.innerHTML = "";
    element.appendChild(container);
  },

  disposeOutputItem(id) {
    // Nothing to clean up
  }
});
