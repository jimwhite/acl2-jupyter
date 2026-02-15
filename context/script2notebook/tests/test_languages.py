"""Tests for script2notebook.languages."""

import pytest

from script2notebook.languages import (
    ACL2,
    COMMON_LISP,
    EXTENSION_MAP,
    LanguageConfig,
    language_for_extension,
)


# ── Extension mapping ────────────────────────────────────────────────

class TestExtensionMap:
    def test_lisp_is_acl2(self):
        assert EXTENSION_MAP[".lisp"] is ACL2

    def test_acl2_is_acl2(self):
        assert EXTENSION_MAP[".acl2"] is ACL2

    def test_lsp_is_common_lisp(self):
        assert EXTENSION_MAP[".lsp"] is COMMON_LISP


class TestLanguageForExtension:
    def test_dot_lisp(self):
        assert language_for_extension(".lisp") is ACL2

    def test_dot_acl2(self):
        assert language_for_extension(".acl2") is ACL2

    def test_dot_lsp(self):
        assert language_for_extension(".lsp") is COMMON_LISP

    def test_without_dot(self):
        assert language_for_extension("lisp") is ACL2

    def test_unsupported_raises(self):
        with pytest.raises(ValueError, match="Unsupported extension"):
            language_for_extension(".py")


# ── LanguageConfig fields ────────────────────────────────────────────

class TestLanguageConfig:
    def test_acl2_kernel_name(self):
        assert ACL2.effective_kernel_name == "acl2"

    def test_common_lisp_kernel_name(self):
        assert COMMON_LISP.effective_kernel_name == "common-lisp"

    def test_acl2_extensions(self):
        assert ".lisp" in ACL2.file_extensions
        assert ".acl2" in ACL2.file_extensions

    def test_common_lisp_extensions(self):
        assert ".lsp" in COMMON_LISP.file_extensions

    def test_effective_kernel_fallback(self):
        lang = LanguageConfig(
            name="test-lang",
            display_name="Test",
            file_extensions=(".tst",),
            kernel_name="",
        )
        assert lang.effective_kernel_name == "test-lang"
