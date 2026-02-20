// ACL2 Events Renderer for VS Code Notebooks
// Renders application/vnd.acl2.events+json output

export const activate = (context) => ({
  renderOutputItem(data, element) {
    const acl2Data = data.json();
    const events = acl2Data.events || [];
    const forms = acl2Data.forms || [];
    const pkg = acl2Data.package || "ACL2";

    // Create container
    const container = document.createElement("div");
    container.style.fontFamily = "var(--vscode-editor-font-family, monospace)";
    container.style.fontSize = "var(--vscode-editor-font-size, 13px)";
    container.style.lineHeight = "1.5";
    container.style.padding = "8px";

    // Package badge
    const pkgBadge = document.createElement("div");
    pkgBadge.style.marginBottom = "8px";
    pkgBadge.style.display = "inline-block";
    pkgBadge.style.padding = "2px 8px";
    pkgBadge.style.borderRadius = "4px";
    pkgBadge.style.backgroundColor = "var(--vscode-badge-background, #4d4d4d)";
    pkgBadge.style.color = "var(--vscode-badge-foreground, #fff)";
    pkgBadge.style.fontSize = "0.85em";
    pkgBadge.textContent = `Package: ${pkg}`;
    container.appendChild(pkgBadge);

    if (events.length === 0 && forms.length === 0) {
      const noEvents = document.createElement("div");
      noEvents.style.color = "var(--vscode-descriptionForeground, #888)";
      noEvents.style.fontStyle = "italic";
      noEvents.textContent = "No events";
      container.appendChild(noEvents);
    } else {
      // Show events
      const count = Math.max(events.length, forms.length);
      for (let i = 0; i < count; i++) {
        const eventBlock = document.createElement("div");
        eventBlock.style.marginTop = "6px";
        eventBlock.style.padding = "6px 8px";
        eventBlock.style.borderRadius = "4px";
        eventBlock.style.backgroundColor = "var(--vscode-editor-background, #1e1e1e)";
        eventBlock.style.border = "1px solid var(--vscode-panel-border, #333)";

        // If we have a form, show it
        if (i < forms.length && forms[i]) {
          const formEl = document.createElement("div");
          formEl.style.color = "var(--vscode-editor-foreground, #d4d4d4)";
          formEl.style.whiteSpace = "pre-wrap";
          formEl.style.wordBreak = "break-word";
          formEl.textContent = forms[i];
          eventBlock.appendChild(formEl);
        }

        // Show the event landmark
        if (i < events.length && events[i]) {
          const eventEl = document.createElement("div");
          eventEl.style.color = "var(--vscode-textPreformat-foreground, #ce9178)";
          eventEl.style.whiteSpace = "pre-wrap";
          eventEl.style.wordBreak = "break-word";
          if (i < forms.length && forms[i]) {
            // If we also showed a form, make the event smaller/lighter
            eventEl.style.fontSize = "0.9em";
            eventEl.style.marginTop = "4px";
            eventEl.style.color = "var(--vscode-descriptionForeground, #888)";
          }
          eventEl.textContent = events[i];
          eventBlock.appendChild(eventEl);
        }

        container.appendChild(eventBlock);
      }
    }

    element.innerHTML = "";
    element.appendChild(container);
  },

  disposeOutputItem(id) {
    // Nothing to clean up
  }
});
