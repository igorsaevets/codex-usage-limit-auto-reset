"""Static contracts for explicit child-process environments."""

from __future__ import annotations

import ast
import unittest
from pathlib import Path
from unittest import mock

import codex_reset_guard as guard
import codex_reset_manager as manager


class ExplicitSubprocessEnvironmentContractTests(unittest.TestCase):
    def assert_all_direct_subprocess_calls_pass_env(self, module_path: Path) -> None:
        source = module_path.read_text(encoding="utf-8")
        tree = ast.parse(source)
        calls = [
            node
            for node in ast.walk(tree)
            if isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id == "subprocess"
            and node.func.attr in {"run", "Popen"}
        ]

        self.assertTrue(calls)
        for call in calls:
            with self.subTest(module=module_path.name, line=call.lineno, function=call.func.attr):
                env_keyword = next(
                    (item.value for item in call.keywords if item.arg == "env"),
                    None,
                )
                self.assertIsNotNone(env_keyword)

    def test_guard_passes_explicit_env_to_every_direct_subprocess_call(self) -> None:
        self.assert_all_direct_subprocess_calls_pass_env(Path(guard.__file__))

    def test_manager_passes_explicit_env_to_every_direct_subprocess_call(self) -> None:
        self.assert_all_direct_subprocess_calls_pass_env(Path(manager.__file__))


class InstallPowerShellEnvironmentContractTests(unittest.TestCase):
    def test_sensitive_launches_use_scrubbed_start_process_helper(self) -> None:
        source = (Path(__file__).resolve().parents[1] / "install.ps1").read_text(
            encoding="utf-8"
        )

        required_snippets = (
            "function Get-SanitizedChildEnvironment",
            "function Invoke-WithScrubbedProcessEnvironment",
            "function Start-ScrubbedHiddenProcess",
            "$startInfo = [System.Diagnostics.ProcessStartInfo]::new()",
            "$startInfo.UseShellExecute = $false",
            "$startInfo.Environment.Clear()",
            "Get-SanitizedChildEnvironment -Extra $Environment",
            "Start-ScrubbedHiddenProcess cannot pass an explicit environment when -Verb is used.",
            "Invoke-WithScrubbedProcessEnvironment -Action {",
            "Invoke-WithScrubbedProcessEnvironment `",
            "$process = Start-ScrubbedHiddenProcess",
            "$secondary = Start-ScrubbedHiddenProcess",
            "$replacementUiProcess = Start-ScrubbedHiddenProcess",
            "$null = Start-ScrubbedHiddenProcess",
        )
        for snippet in required_snippets:
            with self.subTest(snippet=snippet):
                self.assertIn(snippet, source)


class ChildEnvironmentHelperTests(unittest.TestCase):
    def test_guard_child_environment_drops_secret_vars_and_sets_codex_homes(self) -> None:
        with mock.patch.dict(
            guard.os.environ,
            {
                "PATH": "test-path",
                "SYSTEMROOT": r"C:\Windows",
                "OPENAI_API_KEY": "secret-openai",
                "HF_TOKEN": "secret-hf",
            },
            clear=True,
        ):
            env = guard._child_process_environment(
                codex_home=Path(r"C:\tmp\codex-home"),
                extra={"FAKE_FLAG": "1"},
            )

        self.assertEqual(env["PATH"], "test-path")
        self.assertEqual(env["SYSTEMROOT"], r"C:\Windows")
        self.assertEqual(
            env["CODEX_HOME"],
            str(Path(r"C:\tmp\codex-home").expanduser().resolve()),
        )
        self.assertEqual(
            env["CODEX_SQLITE_HOME"],
            str(Path(r"C:\tmp\codex-home").expanduser().resolve()),
        )
        self.assertEqual(env["FAKE_FLAG"], "1")
        self.assertNotIn("OPENAI_API_KEY", env)
        self.assertNotIn("HF_TOKEN", env)

    def test_guard_npm_execution_env_starts_from_scrubbed_environment(self) -> None:
        npm = Path(r"C:\safe\node\npm.cmd")
        with mock.patch.dict(
            guard.os.environ,
            {
                "PATH": r"C:\Windows\System32",
                "SYSTEMROOT": r"C:\Windows",
                "OPENAI_API_KEY": "secret-openai",
                "HF_TOKEN": "secret-hf",
            },
            clear=True,
        ):
            env = guard._npm_execution_env(npm)

        self.assertTrue(env["PATH"].startswith(str(npm.parent)))
        self.assertEqual(env["SYSTEMROOT"], r"C:\Windows")
        self.assertNotIn("OPENAI_API_KEY", env)
        self.assertNotIn("HF_TOKEN", env)


if __name__ == "__main__":
    unittest.main()
