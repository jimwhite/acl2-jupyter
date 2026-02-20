"""Language configuration for Common Lisp and ACL2.

Extension mapping:
  .lsp   → Common Lisp (CL)
  .lisp  → ACL2
  .acl2  → ACL2
"""

from dataclasses import dataclass, field


@dataclass(frozen=True)
class LanguageConfig:
    """Describes a Lisp-family language for script↔notebook conversion."""

    name: str
    """Jupyter kernel / language name (e.g. ``"common-lisp"`` or ``"acl2"``)."""

    display_name: str
    """Human-readable name shown in the notebook metadata."""

    file_extensions: tuple[str, ...]
    """File extensions (with leading dot) associated with this language."""

    line_comment_prefix: str = ";"
    """Character(s) that start a line comment."""

    block_comment_open: str = "#|"
    """Opening delimiter for block comments."""

    block_comment_close: str = "|#"
    """Closing delimiter for block comments."""

    mime_type: str = "text/x-common-lisp"

    codemirror_mode: str = "commonlisp"

    pygments_lexer: str = "common-lisp"

    kernel_name: str = ""
    """Jupyter kernel name.  Falls back to *name* when empty."""

    @property
    def effective_kernel_name(self) -> str:
        return self.kernel_name or self.name


COMMON_LISP = LanguageConfig(
    name="common-lisp",
    display_name="Common Lisp",
    file_extensions=(".lsp",),
    kernel_name="common-lisp",
)

ACL2 = LanguageConfig(
    name="acl2",
    display_name="ACL2",
    file_extensions=(".lisp", ".acl2"),
    kernel_name="acl2",
)

# All registered languages, in priority order.
LANGUAGES: list[LanguageConfig] = [ACL2, COMMON_LISP]

# Extension → LanguageConfig lookup (built once at import time).
EXTENSION_MAP: dict[str, LanguageConfig] = {}
for _lang in LANGUAGES:
    for _ext in _lang.file_extensions:
        EXTENSION_MAP[_ext] = _lang


def language_for_extension(ext: str) -> LanguageConfig:
    """Return the ``LanguageConfig`` for *ext* (including the dot).

    Raises ``ValueError`` for unsupported extensions.
    """
    ext = ext if ext.startswith(".") else f".{ext}"
    try:
        return EXTENSION_MAP[ext]
    except KeyError:
        supported = ", ".join(sorted(EXTENSION_MAP))
        raise ValueError(
            f"Unsupported extension {ext!r}.  Supported: {supported}"
        ) from None
