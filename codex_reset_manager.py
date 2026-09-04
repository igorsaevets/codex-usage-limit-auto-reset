#!/usr/bin/env python3
"""Small, fail-closed controller and UI for Codex usage-limit-reset one-shot jobs.

The manager is deliberately incapable of using a reset.  It may inspect the
account through the guard's read-only compatibility probe, disarm an existing
one-shot job, and ask the installer to create another one-shot job.
"""

from __future__ import annotations

import argparse
import contextlib
import ctypes
import hashlib
import importlib.util
import json
import os
import queue
import re
import shutil
import subprocess
import sys
import sysconfig
import threading
import time
import uuid
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from types import ModuleType
from typing import Any, Callable, Mapping, Protocol, Sequence


UTC = timezone.utc
APP_VERSION = "2.7.1"
POLICY_SCHEMA_VERSION = 1
MINIMUM_SCHEDULE_MARGIN_SECONDS = 600
TASK_START_LEAD_SECONDS = 17 * 60
TERMINAL_STATES = {
    "SUCCEEDED",
    "NO_ACTION",
    "FAILED",
    "INDETERMINATE",
    "DISARMED",
    "CLEANED",
    "SUPERSEDED_CLI",
}

APP_ICON_PNG_64_BASE64 = """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"""

_UI_TONE_COLORS = {
    "neutral": "#202124",
    "positive": "#067647",
    "info": "#175CD3",
    "warning": "#B54708",
    "danger": "#B42318",
    "muted": "#667085",
}
_UI_POSITIVE_TEXT = {"On", "Compatible", "Synchronized", "SUCCEEDED", "Scheduled"}
_UI_INFO_TEXT = {"Preparing", "Waiting safely"}
_UI_WARNING_TEXT = {"Needs attention", "NO_ACTION"}
_UI_DANGER_TEXT = {"FAILED", "INDETERMINATE"}
_UI_MUTED_TEXT = {
    "Paused",
    "Not checked",
    "No reservation",
    "No history",
    "No free reset",
    "Not available",
    "Checking...",
    "PENDING",
    "DISARMED",
    "CLEANED",
    "CANCELLED",
    "CANCEL_REQUESTED",
}


def _ui_tone_for_text(value: object) -> str:
    """Return a supplemental visual tone without changing status semantics."""
    text = str(value).strip()
    if "% used" in text:
        try:
            pct = float(text.split("%")[0].strip())
            if pct >= 95.0:
                return "danger"
            if pct >= 80.0:
                return "warning"
            return "positive"
        except Exception:
            return "neutral"
    if text in _UI_POSITIVE_TEXT:
        return "positive"
    if text in _UI_INFO_TEXT:
        return "info"
    if text in _UI_WARNING_TEXT:
        return "warning"
    if text in _UI_DANGER_TEXT:
        return "danger"
    if text in _UI_MUTED_TEXT or text.startswith("SUPERSEDED_"):
        return "muted"
    return "neutral"


NONTERMINAL_STATES = {"UNARMED", "ARMED", "WAITING", "DISPATCHING"}
TRANSIENT_PRE_DISPATCH_FAILURES = {
    "PRE_DISPATCH_RPC_ERROR",
    "PRE_DISPATCH_TRANSPORT_ERROR",
}
SENSITIVE_POLICY_KEYS = {
    "creditid",
    "credit_id",
    "idempotencykey",
    "idempotency_key",
    "email",
    "token",
    "accesstoken",
    "access_token",
    "refreshtoken",
    "refresh_token",
}
WINDOWLESS_SUBPROCESS_FLAGS = (
    subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
)
WINDOWS_CHILD_ENV_ALLOWLIST = {
    "APPDATA",
    "COMSPEC",
    "HOMEDRIVE",
    "HOMEPATH",
    "LOCALAPPDATA",
    "NUMBER_OF_PROCESSORS",
    "OS",
    "PATH",
    "PATHEXT",
    "PROCESSOR_ARCHITECTURE",
    "PROCESSOR_IDENTIFIER",
    "PROGRAMDATA",
    "SYSTEMDRIVE",
    "SYSTEMROOT",
    "TEMP",
    "TMP",
    "USERNAME",
    "USERPROFILE",
    "WINDIR",
}
LINUX_CHILD_ENV_ALLOWLIST = {
    "DBUS_SESSION_BUS_ADDRESS",
    "HOME",
    "LANG",
    "LC_ALL",
    "LC_CTYPE",
    "LOGNAME",
    "PATH",
    "SHELL",
    "TERM",
    "TMPDIR",
    "USER",
    "XDG_CACHE_HOME",
    "XDG_CONFIG_HOME",
    "XDG_DATA_HOME",
    "XDG_RUNTIME_DIR",
    "XDG_STATE_HOME",
}
UI_LOCK_BUSY_CODE = "MANAGER_UI_ALREADY_RUNNING"
UI_LOCK_FILENAME = "manager-ui.lock"
UI_SHOW_REQUEST_FILENAME = "manager-ui-show-request.json"
UI_READY_FILENAME = "manager-ui-ready.json"
# A second launcher and the existing UI normally exchange this marker within
# 250 ms. Keep the window short so an old local file cannot focus a later UI,
# while tolerating timestamp truncation and a small amount of clock skew.
UI_SHOW_REQUEST_MAX_AGE_SECONDS = 30
UI_SHOW_REQUEST_FUTURE_SKEW_SECONDS = 5


def _child_process_environment(
    *, extra: Mapping[str, str] | None = None
) -> dict[str, str]:
    source = os.environ
    allowed = (
        LINUX_CHILD_ENV_ALLOWLIST if sys.platform.startswith("linux") else WINDOWS_CHILD_ENV_ALLOWLIST
    )
    env: dict[str, str] = {}
    for key in allowed:
        value = source.get(key)
        if isinstance(value, str) and value:
            env[key] = value
    if sys.platform.startswith("linux"):
        env.setdefault("PATH", "/usr/bin:/bin")
    if extra:
        for key, value in extra.items():
            if isinstance(value, str) and value:
                env[key] = value
    return env


def _manager_console_python() -> Path:
    """Return the validated console interpreter beside this manager runtime."""
    if sys.platform.startswith("linux"):
        try:
            running = Path(sys.executable).resolve(strict=True)
            gil_probe = getattr(sys, "_is_gil_enabled", None)
            gil_enabled = True if not callable(gil_probe) else gil_probe() is True
            version = sys.version_info
        except (OSError, RuntimeError, TypeError, ValueError) as error:
            raise ManagerError("CHILD_INSTALL_FAILED") from error
        if (
            sys.implementation.name != "cpython"
            or version.major != 3
            or version.minor < 11
            or version.releaselevel != "final"
            or sys.prefix != sys.base_prefix
            or sysconfig.get_config_var("Py_GIL_DISABLED") in {1, "1"}
            or not gil_enabled
            or not running.is_file()
        ):
            raise ManagerError("CHILD_INSTALL_FAILED")
        return running
    try:
        running = Path(sys.executable).resolve(strict=True)
        if running.name.casefold() not in {"python.exe", "pythonw.exe"}:
            raise ValueError("unexpected manager executable name")
        runtime_dir = running.parent
        console = (runtime_dir / "python.exe").resolve(strict=True)
        windowless = (runtime_dir / "pythonw.exe").resolve(strict=True)
    except (OSError, RuntimeError, TypeError, ValueError) as error:
        raise ManagerError("CHILD_INSTALL_FAILED") from error
    if (
        not running.is_file()
        or not console.is_file()
        or not windowless.is_file()
        or console.parent != runtime_dir
        or windowless.parent != runtime_dir
        or console.name.casefold() != "python.exe"
        or windowless.name.casefold() != "pythonw.exe"
        or running not in {console, windowless}
    ):
        raise ManagerError("CHILD_INSTALL_FAILED")
    return console


class ManagerError(Exception):
    """A sanitized manager failure carrying a stable UI/automation code."""

    def __init__(self, code: str, message: str | None = None) -> None:
        super().__init__(message or code)
        self.code = code


class PreserveActiveJobError(ManagerError):
    """A global CLI probe failure that must not cancel a verified pinned job."""


def _utc_text(epoch: int | float) -> str:
    return datetime.fromtimestamp(int(epoch), UTC).strftime("%Y-%m-%dT%H:%M:%SZ")


def _utc_epoch(value: str) -> int:
    if not isinstance(value, str) or not value.endswith("Z"):
        raise ManagerError("MANIFEST_INVALID")
    try:
        return int(datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=UTC).timestamp())
    except ValueError as error:
        raise ManagerError("MANIFEST_INVALID") from error


def _platform_identity(value: str) -> str:
    """Normalize identifiers only on Windows, whose task/path checks are caseless."""
    return value.casefold() if os.name == "nt" else value


def _default_root() -> Path:
    explicit = os.environ.get("CODEX_RESET_MANAGER_ROOT")
    if explicit:
        return Path(explicit).expanduser().resolve()
    if sys.platform.startswith("linux"):
        data_home = os.environ.get("XDG_DATA_HOME")
        base = Path(data_home).expanduser() if data_home else Path.home() / ".local" / "share"
        return (base / "codex-usage-limit-auto-reset").resolve()
    local = os.environ.get("LOCALAPPDATA")
    if not local:
        raise ManagerError("LOCALAPPDATA_UNAVAILABLE")
    return (Path(local) / "CodexResetCredit").resolve()


def _atomic_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{uuid.uuid4().hex}.tmp")
    try:
        with temporary.open("w", encoding="utf-8", newline="\n") as stream:
            json.dump(value, stream, ensure_ascii=False, indent=2, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        with contextlib.suppress(FileNotFoundError):
            temporary.unlink()


def _read_object(path: Path, code: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ManagerError(code) from error
    if not isinstance(value, dict):
        raise ManagerError(code)
    return value


class FileLock:
    """One-byte advisory lock shared by manager processes and the v2 guard."""

    def __init__(self, path: Path, *, busy_code: str) -> None:
        self.path = path
        self.busy_code = busy_code
        self.stream: Any = None

    def __enter__(self) -> "FileLock":
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.stream = self.path.open("a+b")
        self.stream.seek(0, os.SEEK_END)
        if self.stream.tell() == 0:
            self.stream.write(b"0")
            self.stream.flush()
        self.stream.seek(0)
        try:
            if os.name == "nt":
                import msvcrt

                msvcrt.locking(self.stream.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl

                fcntl.flock(self.stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as error:
            self.stream.close()
            self.stream = None
            raise ManagerError(self.busy_code) from error
        return self

    def __exit__(self, exc_type: object, exc: object, tb: object) -> None:
        if self.stream is None:
            return
        with contextlib.suppress(OSError):
            self.stream.seek(0)
            if os.name == "nt":
                import msvcrt

                msvcrt.locking(self.stream.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                import fcntl

                fcntl.flock(self.stream.fileno(), fcntl.LOCK_UN)
        self.stream.close()
        self.stream = None


class UiInstanceLease:
    """Lifetime UI lock plus a secret-free request channel for an existing UI."""

    def __init__(self, state_dir: Path, *, now: Callable[[], float] = time.time) -> None:
        self.state_dir = state_dir
        self.lock_path = state_dir / UI_LOCK_FILENAME
        self.show_request_path = state_dir / UI_SHOW_REQUEST_FILENAME
        self.ready_path = state_dir / UI_READY_FILENAME
        self.now = now
        self._lock: FileLock | None = None
        self._ready_published = False

    def acquire(self) -> bool:
        lock = FileLock(self.lock_path, busy_code=UI_LOCK_BUSY_CODE)
        try:
            lock.__enter__()
        except ManagerError as error:
            if error.code != UI_LOCK_BUSY_CODE:
                raise
            self.request_show()
            return False
        self._lock = lock
        # A marker left by a process that no longer owns the lock must never
        # surprise a newly started UI.
        for stale_path in (self.show_request_path, self.ready_path):
            with contextlib.suppress(OSError):
                stale_path.unlink()
        return True

    def request_show(self) -> None:
        try:
            _atomic_json(
                self.show_request_path,
                {
                    "schemaVersion": 1,
                    "request": "show",
                    "requestedAtUtc": _utc_text(self.now()),
                    "requestId": str(uuid.uuid4()),
                },
            )
        except OSError as error:
            raise ManagerError("UI_SHOW_REQUEST_FAILED") from error

    def consume_show_request(self) -> bool:
        if not self.show_request_path.is_file():
            return False
        requested = False
        try:
            value = _read_object(self.show_request_path, "UI_SHOW_REQUEST_INVALID")
            if set(value) != {
                "schemaVersion",
                "request",
                "requestedAtUtc",
                "requestId",
            }:
                raise ManagerError("UI_SHOW_REQUEST_INVALID")
            requested_at = _utc_epoch(value.get("requestedAtUtc"))
            request_id_text = value.get("requestId")
            if not isinstance(request_id_text, str):
                raise ManagerError("UI_SHOW_REQUEST_INVALID")
            try:
                request_id = uuid.UUID(request_id_text)
            except (ValueError, AttributeError) as error:
                raise ManagerError("UI_SHOW_REQUEST_INVALID") from error
            age = self.now() - requested_at
            requested = (
                type(value.get("schemaVersion")) is int
                and value["schemaVersion"] == 1
                and value.get("request") == "show"
                and request_id.version == 4
                and str(request_id) == request_id_text
                and -UI_SHOW_REQUEST_FUTURE_SKEW_SECONDS
                <= age
                <= UI_SHOW_REQUEST_MAX_AGE_SECONDS
            )
        except ManagerError:
            requested = False
        finally:
            with contextlib.suppress(OSError):
                self.show_request_path.unlink()
        return requested

    @property
    def ready_published(self) -> bool:
        return self._ready_published

    def publish_ready(self, manager_path: Path) -> None:
        """Publish a secret-free handshake after Explorer accepted the tray icon."""
        if self._lock is None:
            raise ManagerError("UI_READY_WITHOUT_LOCK")
        self.clear_ready()
        try:
            _publish_ui_ready(
                self.state_dir,
                manager_path=manager_path,
                pid=os.getpid(),
                now=self.now,
            )
        except OSError as error:
            self.clear_ready()
            raise ManagerError("UI_READY_PUBLISH_FAILED") from error
        self._ready_published = True

    def clear_ready(self) -> None:
        self._ready_published = False
        with contextlib.suppress(OSError):
            self.ready_path.unlink()

    def release(self) -> None:
        self.clear_ready()
        with contextlib.suppress(OSError):
            self.show_request_path.unlink()
        if self._lock is not None:
            self._lock.__exit__(None, None, None)
            self._lock = None

    def __enter__(self) -> "UiInstanceLease":
        if not self.acquire():
            raise ManagerError(UI_LOCK_BUSY_CODE)
        return self

    def __exit__(self, exc_type: object, exc: object, tb: object) -> None:
        self.release()


@dataclass(frozen=True)
class Job:
    path: Path
    schema_version: int
    job_id: str
    state: str
    armed: bool
    credit_sha256: str
    expires_at: int
    granted_at: int
    reset_type: str
    account_sha256: str
    codex_exe: str
    codex_version: str
    codex_sha256: str
    signer_subject: str
    task_name: str | None
    trigger_at: int
    process_at: int
    phase: str
    result: str | None
    failure_code: str | None
    terminal_at: str | None

    @property
    def terminal(self) -> bool:
        return self.state in TERMINAL_STATES

    @property
    def pre_dispatch(self) -> bool:
        return self.phase == "preDispatch"


@dataclass(frozen=True)
class Credit:
    credit_sha256: str
    expires_at: int
    granted_at: int
    reset_type: str
    status: str


@dataclass(frozen=True)
class ScheduledTask:
    name: str
    enabled: bool


def _read_job(path: Path) -> Job:
    raw = _read_object(path, "MANIFEST_INVALID")
    try:
        schema = raw["schemaVersion"]
        if schema not in {1, 2}:
            raise ValueError
        job_id = str(uuid.UUID(str(raw["jobId"])))
        state = raw["state"]
        armed = raw["armed"]
        target = raw["target"]
        account = raw["account"]
        runtime = raw["runtime"]
        schedule = raw["schedule"]
        task = raw["task"]
        if state not in TERMINAL_STATES | NONTERMINAL_STATES or type(armed) is not bool:
            raise ValueError
        credit_hash = target["creditIdSha256"]
        account_hash = account["emailSha256"]
        if not re.fullmatch(r"[0-9a-f]{64}", credit_hash):
            raise ValueError
        if not re.fullmatch(r"[0-9a-f]{64}", account_hash):
            raise ValueError
        expires = target["expiresAt"]
        granted = target["grantedAt"]
        if type(expires) is not int or type(granted) is not int:
            raise ValueError
        reset_type = target["resetType"]
        if reset_type != "codexRateLimits":
            raise ValueError
        trigger = _utc_epoch(schedule["triggerAtUtc"])
        process = _utc_epoch(schedule["processAtUtc"])
        if trigger != expires - TASK_START_LEAD_SECONDS:
            raise ValueError
        execution = raw.get("execution") if schema == 2 else None
        if schema == 2:
            if not isinstance(execution, Mapping):
                raise ValueError
            phase = execution.get("phase")
            result = execution.get("result")
            failure_code = execution.get("failureCode")
            terminal_at = execution.get("terminalAt")
            if phase not in {"preDispatch", "postDispatch"}:
                raise ValueError
            if result is not None and not isinstance(result, str):
                raise ValueError
            if failure_code is not None and not isinstance(failure_code, str):
                raise ValueError
            if failure_code is not None and re.fullmatch(
                r"[A-Z][A-Z0-9_]{2,63}", failure_code
            ) is None:
                raise ValueError
            if terminal_at is not None and not isinstance(terminal_at, str):
                raise ValueError
            if terminal_at is not None:
                try:
                    _utc_epoch(terminal_at)
                except ManagerError as error:
                    raise ValueError from error
            if state in TERMINAL_STATES and (result != state or terminal_at is None):
                raise ValueError
            if state not in TERMINAL_STATES and any(
                item is not None for item in (result, failure_code, terminal_at)
            ):
                raise ValueError
        else:
            phase = "postDispatch" if state in {"DISPATCHING", "SUCCEEDED", "NO_ACTION", "INDETERMINATE"} else "preDispatch"
            result = state if state in TERMINAL_STATES else None
            failure_code = None
            terminal_at = None
        task_name = task.get("name")
        if task_name is not None and not isinstance(task_name, str):
            raise ValueError
        return Job(
            path=path.resolve(),
            schema_version=schema,
            job_id=job_id,
            state=state,
            armed=armed,
            credit_sha256=credit_hash,
            expires_at=expires,
            granted_at=granted,
            reset_type=reset_type,
            account_sha256=account_hash,
            codex_exe=runtime["codexExe"],
            codex_version=runtime["codexVersion"],
            codex_sha256=runtime["codexSha256"],
            signer_subject=runtime["signerSubject"],
            task_name=task_name,
            trigger_at=trigger,
            process_at=process,
            phase=phase,
            result=result,
            failure_code=failure_code,
            terminal_at=terminal_at,
        )
    except (KeyError, TypeError, ValueError) as error:
        raise ManagerError("MANIFEST_INVALID") from error


def _default_policy(now: float) -> dict[str, Any]:
    at = _utc_text(now)
    return {
        "schemaVersion": POLICY_SCHEMA_VERSION,
        "enabled": False,
        "createdAtUtc": at,
        "updatedAtUtc": at,
        "accountEmailSha256": None,
        "currentJob": None,
        "approvedCli": None,
        "runtimeInstaller": None,
        "runtimeGuard": None,
        "blocked": None,
        "quarantine": [],
        "lastResult": None,
        "lastSyncAtUtc": None,
    }


def _validate_policy(policy: Mapping[str, Any]) -> None:
    expected = set(_default_policy(0))
    if set(policy) != expected or policy.get("schemaVersion") != POLICY_SCHEMA_VERSION:
        raise ManagerError("POLICY_INVALID")
    if type(policy.get("enabled")) is not bool:
        raise ManagerError("POLICY_INVALID")
    account = policy.get("accountEmailSha256")
    if account is not None and not re.fullmatch(r"[0-9a-f]{64}", str(account)):
        raise ManagerError("POLICY_INVALID")
    current = policy.get("currentJob")
    if current is not None:
        if not isinstance(current, Mapping) or set(current) != {"jobId", "manifestPath"}:
            raise ManagerError("POLICY_INVALID")
        try:
            uuid.UUID(str(current["jobId"]))
        except ValueError as error:
            raise ManagerError("POLICY_INVALID") from error
        if not isinstance(current.get("manifestPath"), str) or not current["manifestPath"]:
            raise ManagerError("POLICY_INVALID")
    approved = policy.get("approvedCli")
    if approved is not None:
        required = {"codexExe", "codexVersion", "codexSha256", "signerSubject", "approvedAtUtc"}
        if not isinstance(approved, Mapping) or set(approved) != required:
            raise ManagerError("POLICY_INVALID")
        if not re.fullmatch(r"[0-9a-fA-F]{64}", str(approved.get("codexSha256"))):
            raise ManagerError("POLICY_INVALID")
    blocked = policy.get("blocked")
    if blocked is not None and (
        not isinstance(blocked, Mapping) or set(blocked) != {"code", "atUtc"}
    ):
        raise ManagerError("POLICY_INVALID")
    if blocked is not None and not re.fullmatch(r"[A-Z][A-Z0-9_]{2,63}", str(blocked.get("code"))):
        raise ManagerError("POLICY_INVALID")
    last_result = policy.get("lastResult")
    if last_result is not None:
        required = {"state", "atUtc", "expiresAtUtc", "failureCode"}
        if not isinstance(last_result, Mapping) or set(last_result) != required:
            raise ManagerError("POLICY_INVALID")
        if not isinstance(last_result.get("state"), str):
            raise ManagerError("POLICY_INVALID")
        failure_code = last_result.get("failureCode")
        if failure_code is not None and not re.fullmatch(r"[A-Z][A-Z0-9_]{2,63}", str(failure_code)):
            raise ManagerError("POLICY_INVALID")
    quarantine = policy.get("quarantine")
    if not isinstance(quarantine, list):
        raise ManagerError("POLICY_INVALID")
    for entry in quarantine:
        required = {
            "creditIdSha256",
            "expiresAt",
            "grantedAt",
            "resetType",
            "reason",
            "firstSeenAtUtc",
            "absentObservedAtUtc",
        }
        if not isinstance(entry, Mapping) or set(entry) != required:
            raise ManagerError("POLICY_INVALID")
        if not re.fullmatch(r"[0-9a-f]{64}", str(entry.get("creditIdSha256"))):
            raise ManagerError("POLICY_INVALID")
        if re.fullmatch(r"[A-Z][A-Z0-9_]{2,63}", str(entry.get("reason"))) is None:
            raise ManagerError("POLICY_INVALID")
    _assert_no_policy_secrets(policy)


def _assert_no_policy_secrets(value: Any, key: str | None = None) -> None:
    if key is not None:
        folded = key.casefold()
        if folded in SENSITIVE_POLICY_KEYS:
            raise ManagerError("POLICY_SECRET_REJECTED")
        if folded == "creditidsha256":
            if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value):
                raise ManagerError("POLICY_SECRET_REJECTED")
    if isinstance(value, Mapping):
        for child_key, child in value.items():
            _assert_no_policy_secrets(child, str(child_key))
    elif isinstance(value, list):
        for child in value:
            _assert_no_policy_secrets(child)


def _assert_npm_package_matches_binary(binary: Mapping[str, Any]) -> None:
    """Require the global @openai/codex version to match its native binary."""
    try:
        exe = Path(str(binary["path"])).resolve()
        rendered_version = str(binary["version"])
    except KeyError as error:
        raise ManagerError("CLI_VALIDATION_FAILED") from error
    version_match = re.fullmatch(r"codex-cli (\d+\.\d+\.\d+)", rendered_version)
    if version_match is None:
        raise ManagerError("CLI_VALIDATION_FAILED")
    package_roots = [
        parent
        for parent in exe.parents
        if parent.name.casefold() == "codex"
        and parent.parent.name.casefold() == "@openai"
        and (parent / "package.json").is_file()
    ]
    if len(package_roots) != 1:
        raise ManagerError("CLI_PACKAGE_MISMATCH")
    try:
        package = json.loads((package_roots[0] / "package.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ManagerError("CLI_PACKAGE_MISMATCH") from error
    if not isinstance(package, Mapping) or package.get("version") != version_match.group(1):
        raise ManagerError("CLI_PACKAGE_MISMATCH")


class Services(Protocol):
    def validate_cli(
        self,
        expected_account_sha256: str | None,
        approved_cli: Mapping[str, Any] | None = None,
    ) -> Mapping[str, Any]: ...

    def time_status(self) -> str: ...

    def binary_pin_available(self, job: Job) -> bool: ...

    def validate_task(self, job: Job) -> None: ...

    def consume_tasks(self) -> Sequence[ScheduledTask]: ...

    def disable_task(self, task_name: str) -> None: ...

    def disarm(self, job: Job) -> None: ...

    def create_child(self, installer: Path, codex_path: str, runtime_guard: str | None) -> Mapping[str, Any]: ...

    def notify(self, title: str, message: str, level: str) -> bool: ...


class RealServices:
    def __init__(self, root: Path) -> None:
        self.root = root
        self._guard: ModuleType | None = None

    def _policy_runtime_guard(self) -> Path | None:
        explicit = os.environ.get("CODEX_RESET_MANAGER_RUNTIME_GUARD")
        if explicit:
            return Path(explicit).expanduser().resolve()
        policy_path = self.root / "state" / "policy.json"
        if policy_path.is_file():
            with contextlib.suppress(Exception):
                value = json.loads(policy_path.read_text(encoding="utf-8"))
                path = value.get("runtimeGuard")
                if isinstance(path, str) and path:
                    return Path(path).resolve()
        canonical = Path(__file__).with_name("codex_reset_guard.py")
        if canonical.is_file():
            return canonical.resolve()
        candidates = sorted(Path(__file__).parent.glob("codex_reset_guard-*.py"))
        return candidates[0].resolve() if len(candidates) == 1 else None

    def _guard_module(self) -> ModuleType:
        if self._guard is not None:
            return self._guard
        path = self._policy_runtime_guard()
        if path is None or not path.is_file():
            raise ManagerError("GUARD_RUNTIME_NOT_FOUND")
        spec = importlib.util.spec_from_file_location("codex_reset_guard_runtime", path)
        if spec is None or spec.loader is None:
            raise ManagerError("GUARD_RUNTIME_NOT_FOUND")
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        try:
            spec.loader.exec_module(module)
        except Exception as error:
            raise ManagerError("GUARD_RUNTIME_INVALID") from error
        self._guard = module
        return module

    def validate_cli(
        self,
        expected_account_sha256: str | None,
        approved_cli: Mapping[str, Any] | None = None,
    ) -> Mapping[str, Any]:
        del approved_cli
        guard = self._guard_module()
        try:
            helper = getattr(guard, "validate_cli_compatibility", None)
            if callable(helper):
                result = helper(
                    codex_path=None,
                    codex_home=None,
                    # The controller compares account hashes separately.  A
                    # changed account must not be disguised as a generic CLI
                    # compatibility error, because only the latter may
                    # preserve an already-verified pinned one-shot.
                    expected_account_email_sha256=None,
                )
            else:
                exe = guard._find_native_codex(None)
                guard._validate_cli_schema(exe)
                before = guard._binary_info(exe)
                codex_home = guard._default_codex_home()
                with guard.AppServerTransport(exe, codex_home) as transport:
                    account = guard._account_identity(guard._read_account(transport))
                    rates = guard._read_rate_limits(transport)
                    guard.select_unique_earliest_credit(rates)
                    credits = [
                        {
                            "creditIdSha256": row.id_sha256,
                            "expiresAt": row.expires_at,
                            "grantedAt": row.granted_at,
                            "resetType": row.reset_type,
                            "status": row.status,
                        }
                        for row in guard._credit_records(rates)
                    ]
                after = guard._binary_info(exe)
                if (before.path, before.version, before.sha256) != (after.path, after.version, after.sha256):
                    raise guard.GuardError("binary changed during validation")
                result = {
                    "compatible": True,
                    "binary": {
                        "path": after.path,
                        "version": after.version,
                        "sha256": after.sha256,
                        "signerSubject": after.signer_subject,
                    },
                    "accountEmailSha256": account.email_sha256,
                    "availableCount": len(credits),
                    "credits": credits,
                }
        except Exception as error:
            raise ManagerError("CLI_VALIDATION_FAILED") from error
        if not isinstance(result, Mapping) or result.get("compatible") is not True:
            raise ManagerError("CLI_VALIDATION_FAILED")
        _assert_npm_package_matches_binary(result["binary"])
        return result

    def time_status(self) -> str:
        try:
            return str(self._guard_module()._time_status())
        except Exception as error:
            raise ManagerError("TIME_NOT_SYNCHRONIZED") from error

    def binary_pin_available(self, job: Job) -> bool:
        guard = self._guard_module()
        try:
            observed = guard._binary_info(Path(job.codex_exe), verify_signature=False)
        except Exception:
            return False
        return (
            observed.path.casefold() == str(Path(job.codex_exe).resolve()).casefold()
            and observed.version == job.codex_version
            and observed.sha256.casefold() == job.codex_sha256.casefold()
        )

    def validate_task(self, job: Job) -> None:
        if not job.task_name:
            raise ManagerError("TASK_CONTRACT_INVALID")
        try:
            completed = subprocess.run(
                ["schtasks", "/Query", "/TN", job.task_name, "/XML"],
                capture_output=True,
                text=True,
                errors="replace",
                timeout=20,
                check=False,
                env=_child_process_environment(),
                creationflags=WINDOWLESS_SUBPROCESS_FLAGS,
            )
            if completed.returncode != 0:
                raise ManagerError("TASK_CONTRACT_INVALID")
            root = ET.fromstring(completed.stdout)
            exec_nodes = [node for node in root.iter() if node.tag.rsplit("}", 1)[-1] == "Exec"]
            if len(exec_nodes) != 1:
                raise ManagerError("TASK_CONTRACT_INVALID")
            arguments = next(
                (
                    child.text.strip()
                    for child in list(exec_nodes[0])
                    if child.tag.rsplit("}", 1)[-1] == "Arguments"
                    and child.text
                    and child.text.strip()
                ),
                None,
            )
            command_text = next(
                (
                    child.text.strip()
                    for child in list(exec_nodes[0])
                    if child.tag.rsplit("}", 1)[-1] == "Command"
                    and child.text
                    and child.text.strip()
                ),
                None,
            )
            match = re.fullmatch(r'"([^"]+)" run --manifest "([^"]+)" --live', arguments or "")
            if match is None:
                raise ManagerError("TASK_CONTRACT_INVALID")
            runner = Path(match.group(1)).resolve()
            manifest_from_task = Path(match.group(2)).resolve()
            task_python = Path(command_text or "").resolve()
            runners_root = (self.root / "runners").resolve()
            manager_python = Path(sys.executable).resolve()
            if (
                manifest_from_task != job.path.resolve()
                or runner.parent != runners_root
                or not runner.is_file()
                or not task_python.is_file()
                or task_python.name.casefold() not in {"python.exe", "pythonw.exe"}
                or task_python.parent != manager_python.parent
            ):
                raise ManagerError("TASK_CONTRACT_INVALID")
            if runner.name != "codex_reset_guard.py":
                digest_match = re.fullmatch(r"codex_reset_guard-([0-9a-f]{64})\.py", runner.name)
                if digest_match is None:
                    raise ManagerError("TASK_CONTRACT_INVALID")
                observed = hashlib.sha256(runner.read_bytes()).hexdigest()
                if observed != digest_match.group(1):
                    raise ManagerError("TASK_CONTRACT_INVALID")
            # Run the task's own immutable validator under the exact Python
            # executable named by the task. This preserves adopted v1
            # python.exe tasks while also accepting windowless pythonw.exe
            # tasks created by newer installers.
            script = (
                "import importlib.util,pathlib,sys;"
                "p=pathlib.Path(sys.argv[1]);"
                "s=importlib.util.spec_from_file_location('task_guard',p);"
                "m=importlib.util.module_from_spec(s);sys.modules['task_guard']=m;s.loader.exec_module(m);"
                "q=pathlib.Path(sys.argv[3]);x=m._load_json(q);m._validate_manifest(x);"
                "m._validate_scheduled_task_contract(sys.argv[2],q,x)"
            )
            validation = subprocess.run(
                [str(task_python), "-I", "-c", script, str(runner), job.task_name, str(job.path)],
                capture_output=True,
                text=True,
                errors="replace",
                timeout=30,
                check=False,
                env=_child_process_environment(),
                creationflags=WINDOWLESS_SUBPROCESS_FLAGS,
            )
            if validation.returncode != 0:
                raise ManagerError("TASK_CONTRACT_INVALID")
        except ManagerError:
            raise
        except Exception as error:
            raise ManagerError("TASK_CONTRACT_INVALID") from error

    def consume_tasks(self) -> Sequence[ScheduledTask]:
        powershell = shutil.which("powershell.exe") or shutil.which("pwsh")
        if not powershell:
            raise ManagerError("TASK_ENUMERATION_FAILED")
        script = (
            "$ErrorActionPreference='Stop';"
            "[Console]::OutputEncoding=[Text.UTF8Encoding]::new($false);"
            "$rows=@(Get-ScheduledTask -TaskPath '\\CodexResetCredit\\' "
            "-ErrorAction SilentlyContinue | Where-Object {$_.TaskName -like 'Consume-*'} | "
            "ForEach-Object {[pscustomobject]@{name=($_.TaskPath+$_.TaskName);"
            "enabled=[bool]$_.Settings.Enabled}});"
            "ConvertTo-Json -InputObject $rows -Compress"
        )
        try:
            completed = subprocess.run(
                [powershell, "-NoProfile", "-NonInteractive", "-Command", script],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=30,
                check=False,
                env=_child_process_environment(),
                creationflags=WINDOWLESS_SUBPROCESS_FLAGS,
            )
            if completed.returncode != 0:
                raise ManagerError("TASK_ENUMERATION_FAILED")
            raw = json.loads(completed.stdout.strip() or "[]")
            if not isinstance(raw, list):
                raise ManagerError("TASK_ENUMERATION_FAILED")
            tasks: list[ScheduledTask] = []
            seen: set[str] = set()
            for row in raw:
                if not isinstance(row, Mapping) or set(row) != {"name", "enabled"}:
                    raise ManagerError("TASK_ENUMERATION_FAILED")
                name = row["name"]
                enabled = row["enabled"]
                if (
                    not isinstance(name, str)
                    or re.fullmatch(
                        r"\\CodexResetCredit\\Consume-[^\\]+", name, re.IGNORECASE
                    )
                    is None
                    or type(enabled) is not bool
                    or name.casefold() in seen
                ):
                    raise ManagerError("TASK_ENUMERATION_FAILED")
                seen.add(name.casefold())
                tasks.append(ScheduledTask(name=name, enabled=enabled))
            return tasks
        except ManagerError:
            raise
        except (OSError, subprocess.TimeoutExpired, json.JSONDecodeError) as error:
            raise ManagerError("TASK_ENUMERATION_FAILED") from error

    def disable_task(self, task_name: str) -> None:
        if (
            not isinstance(task_name, str)
            or re.fullmatch(
                r"\\CodexResetCredit\\Consume-[^\\]+", task_name, re.IGNORECASE
            )
            is None
        ):
            raise ManagerError("TASK_DISABLE_FAILED")
        try:
            completed = subprocess.run(
                ["schtasks", "/Change", "/TN", task_name, "/Disable"],
                capture_output=True,
                text=True,
                errors="replace",
                timeout=20,
                check=False,
                env=_child_process_environment(),
                creationflags=WINDOWLESS_SUBPROCESS_FLAGS,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise ManagerError("TASK_DISABLE_FAILED") from error
        if completed.returncode != 0:
            raise ManagerError("TASK_DISABLE_FAILED")

    def disarm(self, job: Job) -> None:
        try:
            self._guard_module()._disarm(job.path)
        except Exception as error:
            raise ManagerError("DISARM_FAILED") from error

    def create_child(self, installer: Path, codex_path: str, runtime_guard: str | None) -> Mapping[str, Any]:
        pwsh = shutil.which("pwsh")
        if not pwsh:
            raise ManagerError("POWERSHELL_NOT_FOUND")
        manager_python = _manager_console_python()
        env = _child_process_environment()
        if runtime_guard:
            env["CODEX_RESET_MANAGER_RUNTIME_GUARD"] = runtime_guard
        try:
            completed = subprocess.run(
                [
                    pwsh,
                    "-NoProfile",
                    "-NonInteractive",
                    "-File",
                    str(installer),
                    "-ManagerChildOnly",
                    "-PythonPath",
                    str(manager_python),
                    "-CodexPath",
                    codex_path,
                    "-Confirm:$false",
                ],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=180,
                check=False,
                env=env,
                creationflags=WINDOWLESS_SUBPROCESS_FLAGS,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise ManagerError("CHILD_INSTALL_FAILED") from error
        if completed.returncode != 0:
            raise ManagerError("CHILD_INSTALL_FAILED")
        for line in reversed(completed.stdout.splitlines()):
            with contextlib.suppress(json.JSONDecodeError):
                parsed = json.loads(line)
                if isinstance(parsed, Mapping):
                    return parsed
        raise ManagerError("CHILD_INSTALL_OUTPUT_INVALID")

    def notify(self, title: str, message: str, level: str) -> bool:
        return _shell_notification(title, message, level)


class LinuxServices(RealServices):
    """systemd user-manager backend for the headless Linux controller."""

    supports_approved_cli_cache = True
    _TASK_PATTERN = r"codex-reset-consume-[0-9a-f]{12}-[0-9a-f]{8}\.timer"

    @staticmethod
    def _systemctl_environment() -> dict[str, str]:
        environment = _child_process_environment()
        environment.update(
            {
                "LC_ALL": "C",
                "SYSTEMD_COLORS": "0",
                "SYSTEMD_PAGER": "cat",
            }
        )
        return environment

    @staticmethod
    def _systemctl() -> str:
        executable = shutil.which("systemctl")
        if not executable:
            raise ManagerError("SYSTEMD_UNAVAILABLE")
        return executable

    def validate_cli(
        self,
        expected_account_sha256: str | None,
        approved_cli: Mapping[str, Any] | None = None,
    ) -> Mapping[str, Any]:
        del expected_account_sha256
        guard = self._guard_module()
        helper = getattr(guard, "validate_cli_compatibility", None)
        if not callable(helper):
            raise ManagerError("CLI_VALIDATION_FAILED")
        trusted_binary: Mapping[str, Any] | None = None
        try:
            if isinstance(approved_cli, Mapping):
                observe = getattr(guard, "observe_cli_pin", None)
                if not callable(observe):
                    raise ManagerError("CLI_VALIDATION_FAILED")
                current = observe(codex_path=None)
                approved_path = Path(str(approved_cli["codexExe"])).resolve()
                approved_sha256 = str(approved_cli["codexSha256"]).lower()
                if (
                    Path(str(current["path"])).resolve() == approved_path
                    and str(current["version"]) == str(approved_cli["codexVersion"])
                    and str(current["sha256"]).lower() == approved_sha256
                ):
                    trusted_binary = approved_cli
            result = helper(
                codex_path=None,
                codex_home=None,
                # Account identity changes are classified by Controller after
                # the complete response has passed strict parsing.
                expected_account_email_sha256=None,
                trusted_binary=trusted_binary,
            )
        except Exception as error:
            raise ManagerError("CLI_VALIDATION_FAILED") from error
        if not isinstance(result, Mapping) or result.get("compatible") is not True:
            raise ManagerError("CLI_VALIDATION_FAILED")
        binary = result.get("binary")
        if not isinstance(binary, Mapping):
            raise ManagerError("CLI_VALIDATION_FAILED")
        _assert_npm_package_matches_binary(binary)
        return result

    def binary_pin_available(self, job: Job) -> bool:
        guard = self._guard_module()
        try:
            helper = getattr(guard, "observe_pinned_cli_pin", None)
            if callable(helper):
                observed = helper(job.codex_exe)
            else:
                helper = getattr(guard, "observe_cli_pin", None)
                if callable(helper):
                    observed = helper(codex_path=job.codex_exe)
                else:
                    fallback = guard._binary_info(
                        Path(job.codex_exe), verify_signature=False
                    )
                    observed = {
                        "path": fallback.path,
                        "version": fallback.version,
                        "sha256": fallback.sha256,
                    }
            path = str(observed["path"])
            version = str(observed["version"])
            sha256 = str(observed["sha256"])
            return (
                Path(path).resolve() == Path(job.codex_exe).resolve()
                and version == job.codex_version
                and sha256 == job.codex_sha256
            )
        except Exception:
            return False

    def validate_task(self, job: Job) -> None:
        if not isinstance(job.task_name, str) or re.fullmatch(self._TASK_PATTERN, job.task_name) is None:
            raise ManagerError("TASK_CONTRACT_INVALID")
        guard = self._guard_module()
        try:
            manifest = guard._load_json(job.path)
            guard._validate_manifest(manifest)
            guard._validate_scheduled_task_contract(job.task_name, job.path, manifest)
        except Exception as error:
            in_progress = getattr(guard, "SystemdTriggerInProgressError", None)
            if isinstance(in_progress, type) and isinstance(error, in_progress):
                raise ManagerError("TASK_TRIGGER_IN_PROGRESS") from error
            elapsed = getattr(guard, "SystemdTriggerElapsedError", None)
            if isinstance(elapsed, type) and isinstance(error, elapsed):
                raise ManagerError("PRE_DISPATCH_TRIGGER_ELAPSED") from error
            raise ManagerError("TASK_CONTRACT_INVALID") from error

    def consume_tasks(self) -> Sequence[ScheduledTask]:
        systemctl = self._systemctl()
        environment = self._systemctl_environment()
        try:
            inventory_commands = (
                [
                    systemctl,
                    "--user",
                    "list-unit-files",
                    "--type=timer",
                    "--no-legend",
                    "--no-pager",
                    "--plain",
                ],
                [
                    systemctl,
                    "--user",
                    "list-units",
                    "--all",
                    "--type=timer",
                    "--no-legend",
                    "--no-pager",
                    "--plain",
                ],
            )
            names: set[str] = set()
            for command in inventory_commands:
                completed = subprocess.run(
                    command,
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    timeout=30,
                    check=False,
                    env=environment,
                    creationflags=WINDOWLESS_SUBPROCESS_FLAGS,
                )
                if completed.returncode != 0:
                    raise ManagerError("TASK_ENUMERATION_FAILED")
                observed_in_command: set[str] = set()
                for line in completed.stdout.splitlines():
                    fields = line.split()
                    if not fields:
                        continue
                    name = fields[0]
                    if not (
                        name.startswith("codex-reset-consume-")
                        and name.endswith(".timer")
                    ):
                        continue
                    if (
                        re.fullmatch(self._TASK_PATTERN, name) is None
                        or name in observed_in_command
                    ):
                        raise ManagerError("TASK_ENUMERATION_FAILED")
                    observed_in_command.add(name)
                    names.add(name)
            tasks: list[ScheduledTask] = []
            for name in sorted(names):
                state = subprocess.run(
                    [
                        systemctl,
                        "--user",
                        "show",
                        "--no-pager",
                        "--property=UnitFileState",
                        "--property=ActiveState",
                        name,
                    ],
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    timeout=20,
                    check=False,
                    env=environment,
                    creationflags=WINDOWLESS_SUBPROCESS_FLAGS,
                )
                if state.returncode != 0:
                    raise ManagerError("TASK_ENUMERATION_FAILED")
                properties: dict[str, str] = {}
                for line in state.stdout.splitlines():
                    if "=" not in line:
                        continue
                    key, value = line.split("=", 1)
                    if key in properties:
                        raise ManagerError("TASK_ENUMERATION_FAILED")
                    properties[key] = value
                if set(properties) != {"UnitFileState", "ActiveState"}:
                    raise ManagerError("TASK_ENUMERATION_FAILED")
                unit_state = properties["UnitFileState"]
                active_state = properties["ActiveState"]
                if unit_state not in {"enabled", "disabled"} or active_state not in {
                    "active",
                    "inactive",
                    "failed",
                }:
                    raise ManagerError("TASK_ENUMERATION_FAILED")
                tasks.append(
                    ScheduledTask(
                        name=name,
                        enabled=unit_state == "enabled" or active_state == "active",
                    )
                )
            return tasks
        except ManagerError:
            raise
        except (OSError, subprocess.TimeoutExpired) as error:
            raise ManagerError("TASK_ENUMERATION_FAILED") from error

    def disable_task(self, task_name: str) -> None:
        if not isinstance(task_name, str) or re.fullmatch(self._TASK_PATTERN, task_name) is None:
            raise ManagerError("TASK_DISABLE_FAILED")
        try:
            disabled = self._guard_module()._disable_task_best_effort(task_name)
        except Exception as error:
            raise ManagerError("TASK_DISABLE_FAILED") from error
        if disabled is not True:
            raise ManagerError("TASK_DISABLE_FAILED")

    def create_child(
        self,
        installer: Path,
        codex_path: str,
        runtime_guard: str | None,
    ) -> Mapping[str, Any]:
        manager_python = _manager_console_python()
        guard_path = (
            Path(runtime_guard).expanduser().resolve()
            if runtime_guard
            else self._policy_runtime_guard()
        )
        try:
            installer_path = installer.expanduser().resolve(strict=True)
            if guard_path is None:
                raise OSError("guard path is missing")
            guard_path = guard_path.resolve(strict=True)
        except (OSError, RuntimeError) as error:
            raise ManagerError("CHILD_INSTALL_FAILED") from error
        if (
            not installer_path.is_file()
            or installer_path.suffix != ".py"
            or not guard_path.is_file()
            or guard_path.suffix != ".py"
        ):
            raise ManagerError("CHILD_INSTALL_FAILED")
        try:
            completed = subprocess.run(
                [
                    str(manager_python),
                    "-I",
                    str(installer_path),
                    "--manager-child-only",
                    "--install-root",
                    str(self.root),
                    "--python-path",
                    str(manager_python),
                    "--codex-path",
                    codex_path,
                    "--runtime-guard",
                    str(guard_path),
                ],
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=600,
                check=False,
                env=_child_process_environment(),
                creationflags=WINDOWLESS_SUBPROCESS_FLAGS,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise ManagerError("CHILD_INSTALL_FAILED") from error
        if completed.returncode != 0:
            raise ManagerError("CHILD_INSTALL_FAILED")
        for line in reversed(completed.stdout.splitlines()):
            with contextlib.suppress(json.JSONDecodeError):
                parsed = json.loads(line)
                if (
                    isinstance(parsed, Mapping)
                    and set(parsed) == {"manifestPath", "taskName", "jobId"}
                ):
                    return parsed
        raise ManagerError("CHILD_INSTALL_OUTPUT_INVALID")

    def notify(self, title: str, message: str, level: str) -> bool:
        del title, message, level
        return False


def _shell_notification(title: str, message: str, level: str = "info") -> bool:
    """Best-effort Shell_NotifyIconW banner; manager state remains authoritative."""
    if os.name != "nt":
        return False
    hwnd = None
    data = None
    added = False
    try:
        from ctypes import wintypes

        class NOTIFYICONDATAW(ctypes.Structure):
            _fields_ = [
                ("cbSize", wintypes.DWORD),
                ("hWnd", wintypes.HWND),
                ("uID", wintypes.UINT),
                ("uFlags", wintypes.UINT),
                ("uCallbackMessage", wintypes.UINT),
                ("hIcon", wintypes.HICON),
                ("szTip", wintypes.WCHAR * 128),
                ("dwState", wintypes.DWORD),
                ("dwStateMask", wintypes.DWORD),
                ("szInfo", wintypes.WCHAR * 256),
                ("uTimeoutOrVersion", wintypes.UINT),
                ("szInfoTitle", wintypes.WCHAR * 64),
                ("dwInfoFlags", wintypes.DWORD),
                ("guidItem", ctypes.c_byte * 16),
                ("hBalloonIcon", wintypes.HICON),
            ]

        user32 = ctypes.windll.user32
        shell32 = ctypes.windll.shell32
        hwnd = user32.CreateWindowExW(0, "Static", "CodexResetCreditNotice", 0, 0, 0, 0, 0, -3, 0, 0, None)
        if not hwnd:
            return False
        data = NOTIFYICONDATAW()
        data.cbSize = ctypes.sizeof(data)
        data.hWnd = hwnd
        data.uID = 1
        data.uFlags = 0x10  # NIF_INFO
        data.szInfo = message[:255]
        data.szInfoTitle = title[:63]
        data.dwInfoFlags = {"info": 1, "warning": 2, "error": 3}.get(level, 1)
        data.uTimeoutOrVersion = 8_000
        added = bool(shell32.Shell_NotifyIconW(0, ctypes.byref(data)))
        if added:
            # Shell balloons are asynchronous. Keep the owner window and its
            # message pump alive long enough for Windows to display the banner
            # before deleting the temporary notification-area icon.
            end = time.monotonic() + 8.0
            message_record = wintypes.MSG()
            while time.monotonic() < end:
                while user32.PeekMessageW(ctypes.byref(message_record), hwnd, 0, 0, 1):
                    user32.TranslateMessage(ctypes.byref(message_record))
                    user32.DispatchMessageW(ctypes.byref(message_record))
                time.sleep(0.05)
        return added
    except Exception:
        return False
    finally:
        if added and data is not None:
            with contextlib.suppress(Exception):
                ctypes.windll.shell32.Shell_NotifyIconW(2, ctypes.byref(data))
        if hwnd:
            with contextlib.suppress(Exception):
                ctypes.windll.user32.DestroyWindow(hwnd)


class NativeTrayIcon:
    """Persistent Windows notification-area icon backed only by Win32 APIs."""

    COMMAND_OPEN = 1101
    COMMAND_CHECK = 1102
    COMMAND_TOGGLE = 1103
    COMMAND_EXIT = 1104

    def __init__(
        self,
        *,
        on_open: Callable[[], None],
        on_check: Callable[[], None],
        on_toggle: Callable[[], None],
        on_exit: Callable[[], None],
        is_enabled: Callable[[], bool],
    ) -> None:
        self.on_open = on_open
        self.on_check = on_check
        self.on_toggle = on_toggle
        self.on_exit = on_exit
        self.is_enabled = is_enabled
        self._ready = threading.Event()
        self._stop_requested = threading.Event()
        self._icon_available = threading.Event()
        self._thread: threading.Thread | None = None
        self._start_error: Exception | None = None
        self._hwnd: int | None = None

    @property
    def running(self) -> bool:
        return (
            self._thread is not None
            and self._thread.is_alive()
            and self._ready.is_set()
            and self._start_error is None
            and bool(self._hwnd)
            and self._icon_available.is_set()
        )

    @property
    def toggle_menu_text(self) -> str:
        try:
            enabled = bool(self.is_enabled())
        except Exception:
            enabled = False
        return "Pause Automatic Use" if enabled else "Start Automatic Use"

    def start(self, *, timeout: float = 5.0) -> bool:
        if os.name != "nt":
            return False
        if self._thread is not None:
            return self.running
        self._thread = threading.Thread(
            target=self._thread_main,
            name="CodexResetCreditTray",
            daemon=True,
        )
        self._thread.start()
        if not self._ready.wait(timeout):
            self.stop(timeout=timeout)
            return False
        return self.running

    def stop(self, *, timeout: float = 5.0) -> None:
        self._stop_requested.set()
        if self._hwnd:
            with contextlib.suppress(Exception):
                self._post_close(self._hwnd)
        if self._thread is not None and self._thread is not threading.current_thread():
            self._thread.join(timeout)

    def _post_close(self, hwnd: int) -> None:
        ctypes.windll.user32.PostMessageW(hwnd, 0x0010, 0, 0)  # WM_CLOSE

    def _thread_main(self) -> None:
        try:
            self._run_windows()
        except Exception as error:
            self._start_error = error
        finally:
            self._icon_available.clear()
            self._hwnd = None
            self._ready.set()

    def _replace_icon(self, register: Callable[[], bool]) -> bool:
        """Atomically reflect whether Explorer accepted the current tray icon."""
        self._icon_available.clear()
        try:
            installed = bool(register())
        except Exception:
            installed = False
        if installed:
            self._icon_available.set()
        return installed

    @staticmethod
    def _register_notify_icon(shell32: Any, data: Any) -> bool:
        """Add an icon only when Explorer also accepts version-4 semantics."""
        if not shell32.Shell_NotifyIconW(0, ctypes.byref(data)):  # NIM_ADD
            return False
        data.uTimeoutOrVersion = 4  # NOTIFYICON_VERSION_4
        if shell32.Shell_NotifyIconW(4, ctypes.byref(data)):  # NIM_SETVERSION
            return True
        # Without version 4 the callback payload has different semantics;
        # remove the partial registration instead of reporting a usable icon.
        with contextlib.suppress(Exception):
            shell32.Shell_NotifyIconW(2, ctypes.byref(data))  # NIM_DELETE
        return False

    def _dispatch_command(self, command: int) -> None:
        callback = {
            self.COMMAND_OPEN: self.on_open,
            self.COMMAND_CHECK: self.on_check,
            self.COMMAND_TOGGLE: self.on_toggle,
            self.COMMAND_EXIT: self.on_exit,
        }.get(command)
        if callback is not None:
            with contextlib.suppress(Exception):
                callback()

    def _run_windows(self) -> None:
        from ctypes import wintypes

        if not hasattr(ctypes, "WINFUNCTYPE"):
            raise OSError("Win32 callbacks are unavailable")

        WM_APP = 0x8000
        WM_CLOSE = 0x0010
        WM_DESTROY = 0x0002
        WM_LBUTTONDBLCLK = 0x0203
        WM_RBUTTONUP = 0x0205
        WM_CONTEXTMENU = 0x007B
        WM_NULL = 0x0000
        TRAY_CALLBACK = WM_APP + 41
        NIM_DELETE = 2
        NIF_MESSAGE = 0x01
        NIF_ICON = 0x02
        NIF_TIP = 0x04
        MF_STRING = 0x00
        MF_SEPARATOR = 0x800
        TPM_RIGHTBUTTON = 0x0002
        TPM_RETURNCMD = 0x0100
        TPM_NONOTIFY = 0x0080

        WNDPROC = ctypes.WINFUNCTYPE(
            ctypes.c_ssize_t,
            wintypes.HWND,
            wintypes.UINT,
            wintypes.WPARAM,
            wintypes.LPARAM,
        )

        class WNDCLASSW(ctypes.Structure):
            _fields_ = [
                ("style", wintypes.UINT),
                ("lpfnWndProc", WNDPROC),
                ("cbClsExtra", ctypes.c_int),
                ("cbWndExtra", ctypes.c_int),
                ("hInstance", wintypes.HINSTANCE),
                ("hIcon", wintypes.HICON),
                ("hCursor", wintypes.HANDLE),
                ("hbrBackground", wintypes.HBRUSH),
                ("lpszMenuName", wintypes.LPCWSTR),
                ("lpszClassName", wintypes.LPCWSTR),
            ]

        class NOTIFYICONDATAW(ctypes.Structure):
            _fields_ = [
                ("cbSize", wintypes.DWORD),
                ("hWnd", wintypes.HWND),
                ("uID", wintypes.UINT),
                ("uFlags", wintypes.UINT),
                ("uCallbackMessage", wintypes.UINT),
                ("hIcon", wintypes.HICON),
                ("szTip", wintypes.WCHAR * 128),
                ("dwState", wintypes.DWORD),
                ("dwStateMask", wintypes.DWORD),
                ("szInfo", wintypes.WCHAR * 256),
                ("uTimeoutOrVersion", wintypes.UINT),
                ("szInfoTitle", wintypes.WCHAR * 64),
                ("dwInfoFlags", wintypes.DWORD),
                ("guidItem", ctypes.c_byte * 16),
                ("hBalloonIcon", wintypes.HICON),
            ]

        user32 = ctypes.windll.user32
        shell32 = ctypes.windll.shell32
        kernel32 = ctypes.windll.kernel32
        kernel32.GetModuleHandleW.argtypes = [wintypes.LPCWSTR]
        user32.CreateWindowExW.restype = wintypes.HWND
        user32.CreateWindowExW.argtypes = [
            wintypes.DWORD,
            wintypes.LPCWSTR,
            wintypes.LPCWSTR,
            wintypes.DWORD,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_int,
            wintypes.HWND,
            wintypes.HMENU,
            wintypes.HINSTANCE,
            wintypes.LPVOID,
        ]
        user32.RegisterClassW.argtypes = [ctypes.POINTER(WNDCLASSW)]
        user32.RegisterClassW.restype = wintypes.WORD
        user32.UnregisterClassW.argtypes = [wintypes.LPCWSTR, wintypes.HINSTANCE]
        user32.UnregisterClassW.restype = wintypes.BOOL
        user32.LoadIconW.restype = wintypes.HICON
        user32.LoadIconW.argtypes = [wintypes.HINSTANCE, ctypes.c_void_p]
        user32.CreatePopupMenu.restype = wintypes.HMENU
        user32.AppendMenuW.argtypes = [
            wintypes.HMENU,
            wintypes.UINT,
            ctypes.c_size_t,
            wintypes.LPCWSTR,
        ]
        user32.TrackPopupMenu.argtypes = [
            wintypes.HMENU,
            wintypes.UINT,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_int,
            wintypes.HWND,
            wintypes.LPCVOID,
        ]
        user32.TrackPopupMenu.restype = wintypes.UINT
        user32.DestroyMenu.argtypes = [wintypes.HMENU]
        user32.DestroyMenu.restype = wintypes.BOOL
        user32.DestroyWindow.argtypes = [wintypes.HWND]
        user32.DestroyWindow.restype = wintypes.BOOL
        user32.IsWindow.argtypes = [wintypes.HWND]
        user32.IsWindow.restype = wintypes.BOOL
        user32.SetForegroundWindow.argtypes = [wintypes.HWND]
        user32.SetForegroundWindow.restype = wintypes.BOOL
        user32.PostMessageW.argtypes = [
            wintypes.HWND,
            wintypes.UINT,
            wintypes.WPARAM,
            wintypes.LPARAM,
        ]
        user32.PostMessageW.restype = wintypes.BOOL
        user32.DefWindowProcW.argtypes = [
            wintypes.HWND,
            wintypes.UINT,
            wintypes.WPARAM,
            wintypes.LPARAM,
        ]
        user32.DefWindowProcW.restype = ctypes.c_ssize_t
        kernel32.GetModuleHandleW.restype = wintypes.HMODULE

        instance = kernel32.GetModuleHandleW(None)
        class_name = f"CodexResetCreditTray-{os.getpid()}-{uuid.uuid4().hex}"
        icon_data: NOTIFYICONDATAW | None = None
        icon_added = False
        class_registered = False
        taskbar_created = user32.RegisterWindowMessageW("TaskbarCreated")

        def add_icon(hwnd: int) -> bool:
            nonlocal icon_data, icon_added
            icon_added = False
            icon_data = None
            data = NOTIFYICONDATAW()
            data.cbSize = ctypes.sizeof(data)
            data.hWnd = hwnd
            data.uID = 1
            data.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP
            data.uCallbackMessage = TRAY_CALLBACK
            h_custom_icon = None
            ico_candidates = [
                Path(__file__).parent / "assets" / "app_icon.ico",
                Path(os.environ.get("LOCALAPPDATA", "")) / "CodexResetCredit" / "assets" / "app_icon.ico",
            ]
            for candidate in ico_candidates:
                if candidate.is_file():
                    with contextlib.suppress(Exception):
                        h_custom_icon = user32.LoadImageW(
                            None,
                            str(candidate),
                            1,  # IMAGE_ICON
                            user32.GetSystemMetrics(49),  # SM_CXSMICON
                            user32.GetSystemMetrics(50),  # SM_CYSMICON
                            0x00000010,  # LR_LOADFROMFILE
                        )
                        if h_custom_icon:
                            break
            data.hIcon = h_custom_icon or user32.LoadIconW(None, ctypes.c_void_p(32512))
            data.szTip = "Codex Usage Limit Reset Manager"
            if not self._register_notify_icon(shell32, data):
                return False
            icon_data = data
            icon_added = True
            return True

        def show_menu(hwnd: int) -> None:
            menu = user32.CreatePopupMenu()
            if not menu:
                return
            try:
                user32.AppendMenuW(menu, MF_STRING, self.COMMAND_OPEN, "Open Manager")
                user32.AppendMenuW(menu, MF_STRING, self.COMMAND_CHECK, "Check Now")
                user32.AppendMenuW(menu, MF_STRING, self.COMMAND_TOGGLE, self.toggle_menu_text)
                user32.AppendMenuW(menu, MF_SEPARATOR, 0, None)
                user32.AppendMenuW(menu, MF_STRING, self.COMMAND_EXIT, "Exit UI")
                point = wintypes.POINT()
                if not user32.GetCursorPos(ctypes.byref(point)):
                    return
                user32.SetForegroundWindow(hwnd)
                command = user32.TrackPopupMenu(
                    menu,
                    TPM_RIGHTBUTTON | TPM_RETURNCMD | TPM_NONOTIFY,
                    point.x,
                    point.y,
                    0,
                    hwnd,
                    None,
                )
                user32.PostMessageW(hwnd, WM_NULL, 0, 0)
                if command:
                    self._dispatch_command(int(command))
            finally:
                user32.DestroyMenu(menu)

        @WNDPROC
        def window_proc(hwnd: int, message: int, wparam: int, lparam: int) -> int:
            if message == TRAY_CALLBACK:
                mouse_event = int(lparam) & 0xFFFF
                if mouse_event == WM_LBUTTONDBLCLK:
                    self._dispatch_command(self.COMMAND_OPEN)
                elif mouse_event in {WM_RBUTTONUP, WM_CONTEXTMENU}:
                    show_menu(hwnd)
                return 0
            if taskbar_created and message == taskbar_created:
                # Explorer discarded the old registration during its restart.
                # Clear availability first so X can never hide an un-restorable
                # window if re-registration fails.
                self._replace_icon(lambda: add_icon(hwnd))
                return 0
            if message == WM_CLOSE:
                user32.DestroyWindow(hwnd)
                return 0
            if message == WM_DESTROY:
                user32.PostQuitMessage(0)
                return 0
            return int(user32.DefWindowProcW(hwnd, message, wparam, lparam))

        window_class = WNDCLASSW()
        window_class.lpfnWndProc = window_proc
        window_class.hInstance = instance
        window_class.lpszClassName = class_name
        hwnd = None
        try:
            if not user32.RegisterClassW(ctypes.byref(window_class)):
                raise ctypes.WinError()
            class_registered = True
            hwnd = user32.CreateWindowExW(
                0,
                class_name,
                "Codex Usage Limit Reset Manager Tray",
                0,
                0,
                0,
                0,
                0,
                None,
                None,
                instance,
                None,
            )
            if not hwnd:
                raise ctypes.WinError()
            self._hwnd = int(hwnd)
            if not self._replace_icon(lambda: add_icon(self._hwnd)):
                raise ctypes.WinError()
            self._ready.set()
            if self._stop_requested.is_set():
                user32.PostMessageW(hwnd, WM_CLOSE, 0, 0)
            message_record = wintypes.MSG()
            while True:
                result = user32.GetMessageW(ctypes.byref(message_record), None, 0, 0)
                if result == 0:
                    break
                if result == -1:
                    raise ctypes.WinError()
                user32.TranslateMessage(ctypes.byref(message_record))
                user32.DispatchMessageW(ctypes.byref(message_record))
        finally:
            self._icon_available.clear()
            if icon_added and icon_data is not None:
                with contextlib.suppress(Exception):
                    shell32.Shell_NotifyIconW(NIM_DELETE, ctypes.byref(icon_data))
            if hwnd and user32.IsWindow(hwnd):
                with contextlib.suppress(Exception):
                    user32.DestroyWindow(hwnd)
            if class_registered:
                with contextlib.suppress(Exception):
                    user32.UnregisterClassW(class_name, instance)


class Controller:
    def __init__(
        self,
        root: Path,
        *,
        services: Services | None = None,
        now: Callable[[], float] = time.time,
    ) -> None:
        self.root = root.resolve()
        self.state_dir = self.root / "state"
        self.manifest_dir = self.root / "manifests"
        self.policy_path = self.state_dir / "policy.json"
        self.notification_path = self.state_dir / "notifications.json"
        self.controller_lock_path = self.state_dir / "controller.lock"
        self.dispatch_lock_path = self.state_dir / "dispatch.lock"
        self.log_path = self.root / "logs" / "manager.jsonl"
        self.services = services or (
            LinuxServices(self.root) if sys.platform.startswith("linux") else RealServices(self.root)
        )
        self.now = now

    def _controller_lock(self) -> FileLock:
        return FileLock(self.controller_lock_path, busy_code="CONTROLLER_BUSY")

    def _dispatch_lock(self) -> FileLock:
        return FileLock(self.dispatch_lock_path, busy_code="LIVE_DISPATCH_ACTIVE")

    def _runtime_hint(self, name: str, suffix: str) -> str | None:
        value = os.environ.get(name)
        if not value:
            return None
        path = Path(value).expanduser().resolve()
        if not path.is_file() or _platform_identity(path.suffix) != _platform_identity(suffix):
            raise ManagerError("RUNTIME_HINT_INVALID")
        return str(path)

    def _discover_installer(self) -> str | None:
        suffix = ".py" if sys.platform.startswith("linux") else ".ps1"
        explicit = self._runtime_hint("CODEX_RESET_MANAGER_RUNTIME_INSTALLER", suffix)
        if explicit:
            return explicit
        pattern = "*install_linux-*.py" if sys.platform.startswith("linux") else "install-*.ps1"
        candidates = sorted((self.root / "installers").glob(pattern))
        if len(candidates) == 1:
            return str(candidates[0].resolve())
        adjacent_name = "install_linux.py" if sys.platform.startswith("linux") else "install.ps1"
        adjacent = Path(__file__).with_name(adjacent_name)
        return str(adjacent.resolve()) if adjacent.is_file() else None

    def _load_policy(self) -> dict[str, Any]:
        if self.policy_path.exists():
            policy = _read_object(self.policy_path, "POLICY_INVALID")
            _validate_policy(policy)
        else:
            policy = _default_policy(self.now())
        installer_suffix = ".py" if sys.platform.startswith("linux") else ".ps1"
        installer = self._runtime_hint(
            "CODEX_RESET_MANAGER_RUNTIME_INSTALLER", installer_suffix
        )
        guard = self._runtime_hint("CODEX_RESET_MANAGER_RUNTIME_GUARD", ".py")
        if installer:
            policy["runtimeInstaller"] = installer
        elif not policy["runtimeInstaller"]:
            policy["runtimeInstaller"] = self._discover_installer()
        if guard:
            policy["runtimeGuard"] = guard
        _validate_policy(policy)
        return policy

    def _save_policy(self, policy: dict[str, Any]) -> None:
        policy["updatedAtUtc"] = _utc_text(self.now())
        _validate_policy(policy)
        _atomic_json(self.policy_path, policy)

    def _jobs(self) -> list[Job]:
        if not self.manifest_dir.exists():
            return []
        jobs: list[Job] = []
        for path in sorted(self.manifest_dir.glob("*.json")):
            jobs.append(_read_job(path))
        return jobs

    @staticmethod
    def _current_ref(job: Job) -> dict[str, str]:
        return {"jobId": job.job_id, "manifestPath": str(job.path)}

    @staticmethod
    def _ref_job(policy: Mapping[str, Any], jobs: Sequence[Job]) -> Job | None:
        reference = policy.get("currentJob")
        if not isinstance(reference, Mapping):
            return None
        matches = [job for job in jobs if job.job_id == reference.get("jobId")]
        if len(matches) != 1:
            raise ManagerError("CURRENT_JOB_MISSING")
        if _platform_identity(str(matches[0].path)) != _platform_identity(
            str(Path(reference["manifestPath"]).resolve())
        ):
            raise ManagerError("CURRENT_JOB_MISMATCH")
        return matches[0]

    def _adopt(self, policy: dict[str, Any], jobs: Sequence[Job]) -> Job | None:
        active = [job for job in jobs if not job.terminal]
        if len(active) > 1:
            raise ManagerError("MULTIPLE_ACTIVE_JOBS")
        referenced: Job | None = None
        if policy["currentJob"] is not None:
            referenced = self._ref_job(policy, jobs)
        if active:
            candidate = active[0]
            if referenced is not None and referenced.job_id != candidate.job_id and not referenced.terminal:
                raise ManagerError("MULTIPLE_ACTIVE_JOBS")
            policy["currentJob"] = self._current_ref(candidate)
            if policy["accountEmailSha256"] is None:
                policy["accountEmailSha256"] = candidate.account_sha256
            elif policy["accountEmailSha256"] != candidate.account_sha256:
                raise ManagerError("ACCOUNT_CHANGED")
            if policy["approvedCli"] is None:
                policy["approvedCli"] = {
                    "codexExe": candidate.codex_exe,
                    "codexVersion": candidate.codex_version,
                    "codexSha256": candidate.codex_sha256,
                    "signerSubject": candidate.signer_subject,
                    "approvedAtUtc": _utc_text(self.now()),
                }
            return candidate
        return referenced

    def _validate_task_inventory(self, jobs: Sequence[Job]) -> None:
        """Require a one-to-one match between enabled consume tasks and live jobs.

        Disabled tasks are immutable audit records and are intentionally
        ignored.  If any enabled task is orphaned or mismatched, every enabled
        consume task is disabled before the controller blocks.
        """
        tasks = list(self.services.consume_tasks())
        enabled = [task for task in tasks if task.enabled]
        enabled_names = [_platform_identity(task.name) for task in enabled]
        expected_jobs = [job for job in jobs if not job.terminal and job.task_name]
        expected_names = [_platform_identity(str(job.task_name)) for job in expected_jobs]
        valid = (
            len(enabled_names) == len(set(enabled_names))
            and len(expected_names) == len(set(expected_names))
            and sorted(enabled_names) == sorted(expected_names)
        )
        if valid:
            return
        for task in enabled:
            self.services.disable_task(task.name)
        raise ManagerError("TASK_INVENTORY_MISMATCH")

    @staticmethod
    def _credits(snapshot: Mapping[str, Any]) -> list[Credit]:
        rows = snapshot.get("credits")
        available_count = snapshot.get("availableCount")
        if not isinstance(rows, list) or type(available_count) is not int or available_count != len(rows):
            raise ManagerError("INVENTORY_INCOMPLETE")
        credits: list[Credit] = []
        hashes: set[str] = set()
        for row in rows:
            if not isinstance(row, Mapping):
                raise ManagerError("INVENTORY_INCOMPLETE")
            digest = row.get("creditIdSha256")
            expires = row.get("expiresAt")
            granted = row.get("grantedAt")
            reset_type = row.get("resetType")
            status = row.get("status")
            if (
                not isinstance(digest, str)
                or not re.fullmatch(r"[0-9a-f]{64}", digest)
                or digest in hashes
                or type(expires) is not int
                or type(granted) is not int
                or reset_type != "codexRateLimits"
                or status != "available"
            ):
                raise ManagerError("INVENTORY_INCOMPLETE")
            hashes.add(digest)
            credits.append(Credit(digest, expires, granted, reset_type, status))
        if credits:
            earliest = min(item.expires_at for item in credits)
            if sum(item.expires_at == earliest for item in credits) != 1:
                raise ManagerError("EARLIEST_EXPIRY_TIED")
        return sorted(credits, key=lambda item: item.expires_at)

    def _validate_runtime(self, policy: dict[str, Any]) -> tuple[Mapping[str, Any], list[Credit]]:
        if getattr(self.services, "supports_approved_cli_cache", False):
            snapshot = self.services.validate_cli(
                policy["accountEmailSha256"], policy.get("approvedCli")
            )
        else:
            snapshot = self.services.validate_cli(policy["accountEmailSha256"])
        account_hash = snapshot.get("accountEmailSha256")
        if not isinstance(account_hash, str) or not re.fullmatch(r"[0-9a-f]{64}", account_hash):
            raise ManagerError("ACCOUNT_RESPONSE_INVALID")
        if (
            policy["accountEmailSha256"] is not None
            and policy["accountEmailSha256"] != account_hash
        ):
            raise ManagerError("ACCOUNT_CHANGED")
        binary = snapshot.get("binary")
        if not isinstance(binary, Mapping):
            raise ManagerError("CLI_VALIDATION_FAILED")
        try:
            approved_at_utc = _utc_text(self.now())
            previous_approval = policy.get("approvedCli")
            if isinstance(previous_approval, Mapping):
                same_binary = (
                    _platform_identity(
                        str(Path(str(previous_approval["codexExe"])).resolve())
                    )
                    == _platform_identity(str(Path(str(binary["path"])).resolve()))
                    and str(previous_approval["codexVersion"])
                    == str(binary["version"])
                    and str(previous_approval["codexSha256"]).lower()
                    == str(binary["sha256"]).lower()
                    and str(previous_approval["signerSubject"])
                    == str(binary["signerSubject"])
                )
                if same_binary and getattr(
                    self.services, "supports_approved_cli_cache", False
                ):
                    approved_at_utc = str(previous_approval["approvedAtUtc"])
            approved = {
                "codexExe": str(Path(str(binary["path"])).resolve()),
                "codexVersion": str(binary["version"]),
                "codexSha256": str(binary["sha256"]).lower(),
                "signerSubject": str(binary["signerSubject"]),
                "approvedAtUtc": approved_at_utc,
            }
        except KeyError as error:
            raise ManagerError("CLI_VALIDATION_FAILED") from error
        if not re.fullmatch(r"[0-9a-f]{64}", approved["codexSha256"]):
            raise ManagerError("CLI_VALIDATION_FAILED")
        credits = self._credits(snapshot)
        # Commit the newly observed identity/pin only after the entire
        # read-only response has passed strict inventory validation.
        if policy["accountEmailSha256"] is None:
            policy["accountEmailSha256"] = account_hash
        policy["approvedCli"] = approved
        return snapshot, credits

    def _block(self, policy: dict[str, Any], code: str) -> None:
        current = policy.get("blocked")
        if not isinstance(current, Mapping) or current.get("code") != code:
            policy["blocked"] = {"code": code, "atUtc": _utc_text(self.now())}
            self._notify_once(
                f"block:{code}",
                "Codex Usage Limit Reset Needs Attention",
                "Automatic scheduling was stopped because a safety check needs attention.",
                "warning",
            )
        self._log("blocked", code=code)

    def _clear_block(self, policy: dict[str, Any]) -> None:
        policy["blocked"] = None

    def _notify_once(self, key: str, title: str, message: str, level: str = "info") -> None:
        record: dict[str, Any] = {}
        if self.notification_path.is_file():
            with contextlib.suppress(Exception):
                record = json.loads(self.notification_path.read_text(encoding="utf-8"))
        if record.get("lastKey") == key:
            return
        delivered = bool(self.services.notify(title, message, level))
        _atomic_json(
            self.notification_path,
            {
                "schemaVersion": 1,
                "lastKey": key,
                "atUtc": _utc_text(self.now()),
                "delivered": delivered,
            },
        )

    def _log(self, event: str, **fields: Any) -> None:
        allowed = {key: value for key, value in fields.items() if key in {"automaticLimitResetAtUtc", "code", "expiresAtUtc", "freeResetExpiresAtUtc", "state"}}
        payload = {"atUtc": _utc_text(self.now()), "event": event, **allowed}
        self.log_path.parent.mkdir(parents=True, exist_ok=True)
        with self.log_path.open("a", encoding="utf-8", newline="\n") as stream:
            stream.write(json.dumps(payload, ensure_ascii=False, sort_keys=True) + "\n")

    @staticmethod
    def _credit_matches_job(credit: Credit, job: Job) -> bool:
        return (
            credit.credit_sha256 == job.credit_sha256
            and credit.expires_at == job.expires_at
            and credit.granted_at == job.granted_at
            and credit.reset_type == job.reset_type
        )

    def _quarantine_credit(self, policy: dict[str, Any], credit: Credit | Job, reason: str) -> None:
        if re.fullmatch(r"[A-Z][A-Z0-9_]{2,63}", reason) is None:
            raise ManagerError("QUARANTINE_REASON_INVALID")
        digest = credit.credit_sha256
        matches = [item for item in policy["quarantine"] if item["creditIdSha256"] == digest]
        if matches:
            entry = matches[0]
            if (
                entry["expiresAt"] != credit.expires_at
                or entry["grantedAt"] != credit.granted_at
                or entry["resetType"] != credit.reset_type
            ):
                raise ManagerError("QUARANTINED_CREDIT_METADATA_CHANGED")
            return
        policy["quarantine"].append(
            {
                "creditIdSha256": digest,
                "expiresAt": credit.expires_at,
                "grantedAt": credit.granted_at,
                "resetType": credit.reset_type,
                "reason": reason,
                "firstSeenAtUtc": _utc_text(self.now()),
                "absentObservedAtUtc": None,
            }
        )

    def _quarantine_barrier(self, policy: dict[str, Any], credits: Sequence[Credit]) -> bool:
        by_hash = {credit.credit_sha256: credit for credit in credits}
        unresolved = False
        for entry in policy["quarantine"]:
            present = by_hash.get(entry["creditIdSha256"])
            if present is not None:
                if entry["absentObservedAtUtc"] is not None:
                    raise ManagerError("QUARANTINED_CREDIT_REAPPEARED")
                if (
                    present.expires_at != entry["expiresAt"]
                    or present.granted_at != entry["grantedAt"]
                    or present.reset_type != entry["resetType"]
                ):
                    raise ManagerError("QUARANTINED_CREDIT_METADATA_CHANGED")
                unresolved = True
            else:
                if entry["absentObservedAtUtc"] is None:
                    entry["absentObservedAtUtc"] = _utc_text(self.now())
                if self.now() < entry["expiresAt"]:
                    unresolved = True
        return unresolved

    def _terminal_reconciled(
        self,
        policy: dict[str, Any],
        job: Job,
        credits: Sequence[Credit],
    ) -> bool:
        """Return True when the terminal job's succession barrier has cleared."""
        policy["lastResult"] = {
            "state": job.state,
            "atUtc": job.terminal_at or _utc_text(self.now()),
            "expiresAtUtc": _utc_text(job.expires_at),
            "failureCode": job.failure_code,
        }
        current = next((credit for credit in credits if credit.credit_sha256 == job.credit_sha256), None)
        if current is not None and not self._credit_matches_job(current, job):
            raise ManagerError("TARGET_METADATA_CHANGED")
        if job.state == "SUCCEEDED":
            self._notify_once(
                f"terminal:{job.job_id}:SUCCEEDED",
                "Codex Usage Limit Reset Used",
                f"The usage limit reset expiring at {_local_time(job.expires_at)} was used safely.",
            )
            return current is None
        if job.state in {"NO_ACTION", "INDETERMINATE"} or (
            job.failure_code == "POST_DISPATCH_NO_CREDIT"
        ):
            self._quarantine_credit(policy, job, job.failure_code or job.state)
            level = "warning" if job.state == "NO_ACTION" else "error"
            self._notify_once(
                f"terminal:{job.job_id}:{job.state}:{job.failure_code}",
                "Codex Usage Limit Reset Result",
                "This reset will not be retried. Automation will continue after it expires.",
                level,
            )
            return self.now() >= job.expires_at and current is None
        if job.state == "FAILED":
            if job.pre_dispatch and job.failure_code in TRANSIENT_PRE_DISPATCH_FAILURES:
                return True
            raise ManagerError(job.failure_code or "JOB_FAILED")
        if job.state in {"DISARMED", "SUPERSEDED_CLI", "CLEANED"}:
            return True
        raise ManagerError("TERMINAL_RESULT_UNKNOWN")

    def _has_margin(self, credit: Credit | Job) -> bool:
        return self.now() <= credit.expires_at - TASK_START_LEAD_SECONDS - MINIMUM_SCHEDULE_MARGIN_SECONDS

    def _installer_path(self, policy: Mapping[str, Any]) -> Path:
        value = policy.get("runtimeInstaller")
        if not isinstance(value, str) or not value:
            raise ManagerError("RUNTIME_INSTALLER_NOT_FOUND")
        path = Path(value).resolve()
        suffix = ".py" if sys.platform.startswith("linux") else ".ps1"
        if not path.is_file() or _platform_identity(path.suffix) != _platform_identity(suffix):
            raise ManagerError("RUNTIME_INSTALLER_NOT_FOUND")
        return path

    def _linux_child_snapshot(self) -> tuple[set[str], set[Path]] | None:
        """Capture only the state needed to undo a failed Linux enrollment."""
        if not isinstance(self.services, LinuxServices):
            return None
        enabled_tasks = {
            _platform_identity(task.name)
            for task in self.services.consume_tasks()
            if task.enabled
        }
        manifests = {
            path.resolve() for path in self.manifest_dir.glob("*.json")
        }
        return enabled_tasks, manifests

    def _cleanup_failed_linux_child(
        self, snapshot: tuple[set[str], set[Path]] | None
    ) -> None:
        """Fail closed if a Linux child exits after partially enrolling a job."""
        if snapshot is None:
            return
        enabled_before, manifests_before = snapshot
        cleanup_failed = False

        # Disable newly-enabled timers before inspecting manifests. A child may
        # have armed a timer and then died while writing an incomplete manifest.
        try:
            tasks_after = list(self.services.consume_tasks())
        except ManagerError:
            tasks_after = []
            cleanup_failed = True
        for task in tasks_after:
            if task.enabled and _platform_identity(task.name) not in enabled_before:
                try:
                    self.services.disable_task(task.name)
                except ManagerError:
                    cleanup_failed = True

        manifests_after = {
            path.resolve() for path in self.manifest_dir.glob("*.json")
        }
        for path in sorted(manifests_after - manifests_before):
            try:
                job = _read_job(path)
            except ManagerError:
                # The timer inventory above remains authoritative for a
                # malformed or partially-written child manifest.
                continue
            if not job.terminal:
                try:
                    self.services.disarm(job)
                except ManagerError:
                    cleanup_failed = True

        if cleanup_failed:
            raise ManagerError("CHILD_INSTALL_CLEANUP_FAILED")

    def _create_child(self, policy: dict[str, Any], credits: Sequence[Credit]) -> Job:
        if not credits:
            raise ManagerError("NO_AVAILABLE_CREDIT")
        earliest = credits[0]
        if not self._has_margin(earliest):
            self._quarantine_credit(policy, earliest, "INSUFFICIENT_LEAD_TIME")
            raise ManagerError("INSUFFICIENT_LEAD_TIME")
        approved = policy.get("approvedCli")
        if not isinstance(approved, Mapping):
            raise ManagerError("CLI_NOT_APPROVED")
        linux_snapshot = self._linux_child_snapshot()
        try:
            self.services.create_child(
                self._installer_path(policy),
                str(approved["codexExe"]),
                policy.get("runtimeGuard"),
            )
            jobs = self._jobs()
            active = [job for job in jobs if not job.terminal]
            if len(active) != 1:
                raise ManagerError("CHILD_JOB_NOT_UNIQUE")
            child = active[0]
            if not self._credit_matches_job(earliest, child):
                raise ManagerError("CHILD_TARGET_MISMATCH")
            policy["currentJob"] = self._current_ref(child)
            self._notify_once(
                f"scheduled:{child.job_id}",
                "Codex Usage Limit Reset Scheduled",
                f"Automatic use is scheduled for {_local_time(child.process_at)}.",
            )
            self._log("scheduled", expiresAtUtc=_utc_text(child.expires_at))
            return child
        except ManagerError as error:
            try:
                self._cleanup_failed_linux_child(linux_snapshot)
            except ManagerError as cleanup_error:
                raise cleanup_error from error
            raise

    def _sync_locked(self, policy: dict[str, Any], jobs: Sequence[Job]) -> dict[str, Any]:
        current = self._adopt(policy, jobs)
        self._validate_task_inventory(jobs)

        # Validate the immutable task contract and its pinned native binary
        # before looking at the mutable global npm installation.  A broken or
        # incompatible newly-installed global CLI must not cancel a healthy
        # already-scheduled one-shot that still has its original binary.
        preserve_on_global_cli_failure = False
        if current is not None and not current.terminal:
            if current.account_sha256 != policy["accountEmailSha256"]:
                raise ManagerError("ACCOUNT_CHANGED")
            try:
                self.services.validate_task(current)
            except ManagerError as error:
                if error.code == "TASK_TRIGGER_IN_PROGRESS":
                    self._save_policy(policy)
                    return self._status_from(
                        policy,
                        current,
                        time_state="unknown",
                        reservation="scheduled",
                    )
                if error.code != "PRE_DISPATCH_TRIGGER_ELAPSED":
                    raise
                self.services.disarm(current)
                self._quarantine_credit(
                    policy, current, "PRE_DISPATCH_TRIGGER_ELAPSED"
                )
                policy["lastResult"] = {
                    "state": "NO_ACTION",
                    "atUtc": _utc_text(self.now()),
                    "expiresAtUtc": _utc_text(current.expires_at),
                    "failureCode": "PRE_DISPATCH_TRIGGER_ELAPSED",
                }
                policy["currentJob"] = None
                self._notify_once(
                    f"terminal:{current.job_id}:NO_ACTION:PRE_DISPATCH_TRIGGER_ELAPSED",
                    "Codex Usage Limit Reset Result",
                    "The scheduled timer elapsed without a confirmed result. "
                    "Automation will continue after this reset expires.",
                    "warning",
                )
                current = None
            if current is not None:
                preserve_on_global_cli_failure = (
                    current.pre_dispatch and self.services.binary_pin_available(current)
                )
        if not policy["enabled"]:
            self._save_policy(policy)
            return self._status_from(policy, current, time_state="unknown")
        self.services.time_status()
        try:
            snapshot, credits = self._validate_runtime(policy)
        except ManagerError as error:
            if preserve_on_global_cli_failure and error.code != "ACCOUNT_CHANGED":
                raise PreserveActiveJobError(error.code) from error
            raise
        del snapshot
        policy["lastSyncAtUtc"] = _utc_text(self.now())
        self._clear_block(policy)
        if self._quarantine_barrier(policy, credits):
            self._save_policy(policy)
            return self._status_from(policy, current, time_state="synchronized", reservation="waiting")

        if current is not None and current.terminal:
            if not self._terminal_reconciled(policy, current, credits):
                self._save_policy(policy)
                return self._status_from(policy, current, time_state="synchronized", reservation="waiting")
            # Quarantine may have been added while reconciling.
            if self._quarantine_barrier(policy, credits):
                self._save_policy(policy)
                return self._status_from(policy, current, time_state="synchronized", reservation="waiting")
            policy["currentJob"] = None
            current = None

        if current is not None:
            if current.account_sha256 != policy["accountEmailSha256"]:
                raise ManagerError("ACCOUNT_CHANGED")
            if current.phase == "postDispatch":
                # A live guard owns dispatch.lock. Seeing a post-dispatch
                # nonterminal manifest after acquiring that lock means the
                # process died between retries. Never issue a new key for it.
                self.services.disarm(current)
                self._quarantine_credit(
                    policy, current, "POST_DISPATCH_PROCESS_LOST"
                )
                policy["lastResult"] = {
                    "state": "INDETERMINATE",
                    "atUtc": _utc_text(self.now()),
                    "expiresAtUtc": _utc_text(current.expires_at),
                    "failureCode": "POST_DISPATCH_UNCONFIRMED",
                }
                policy["currentJob"] = None
                self._save_policy(policy)
                return self._status_from(
                    policy,
                    None,
                    time_state="synchronized",
                    reservation="waiting",
                )
            earliest = credits[0] if credits else None
            target = next((item for item in credits if item.credit_sha256 == current.credit_sha256), None)
            if target is not None and not self._credit_matches_job(target, current):
                raise ManagerError("TARGET_METADATA_CHANGED")
            if target is None:
                self.services.disarm(current)
                self._quarantine_credit(policy, current, "TARGET_MISSING")
                policy["lastResult"] = {
                    "state": "NO_ACTION",
                    "atUtc": _utc_text(self.now()),
                    "expiresAtUtc": _utc_text(current.expires_at),
                    "failureCode": "PRE_DISPATCH_TARGET_MISSING",
                }
                policy["currentJob"] = None
                if self.now() < current.expires_at:
                    self._save_policy(policy)
                    return self._status_from(
                        policy,
                        None,
                        time_state="synchronized",
                        reservation="waiting",
                    )
                current = None
            elif earliest is not None and earliest.credit_sha256 != current.credit_sha256:
                self.services.disarm(current)
                policy["lastResult"] = {
                    "state": "SUPERSEDED_EARLIER",
                    "atUtc": _utc_text(self.now()),
                    "expiresAtUtc": _utc_text(current.expires_at),
                    "failureCode": None,
                }
                policy["currentJob"] = None
                current = None
                if not self._has_margin(earliest):
                    self._quarantine_credit(policy, earliest, "EARLIER_CREDIT_TOO_LATE")
                    self._save_policy(policy)
                    return self._status_from(policy, None, time_state="synchronized", reservation="waiting")
            elif not self.services.binary_pin_available(current):
                self.services.disarm(current)
                policy["currentJob"] = None
                if not self._has_margin(current):
                    self._quarantine_credit(policy, current, "CLI_CHANGED_TOO_LATE")
                    self._save_policy(policy)
                    return self._status_from(policy, None, time_state="synchronized", reservation="waiting")
                current = None
            else:
                # The exact task contract was validated before the mutable
                # global CLI probe above.
                pass

        if current is None:
            if not credits:
                self._save_policy(policy)
                return self._status_from(policy, None, time_state="synchronized", reservation="none")
            if not self._has_margin(credits[0]):
                self._quarantine_credit(policy, credits[0], "INSUFFICIENT_LEAD_TIME")
                self._save_policy(policy)
                return self._status_from(
                    policy,
                    None,
                    time_state="synchronized",
                    reservation="waiting",
                )
            current = self._create_child(policy, credits)
        self._save_policy(policy)
        return self._status_from(policy, current, time_state="synchronized")

    def _mutating_operation(self, operation: Callable[[dict[str, Any], list[Job]], dict[str, Any]]) -> dict[str, Any]:
        with self._controller_lock():
            policy = self._load_policy()
            jobs: list[Job] = []
            try:
                with self._dispatch_lock():
                    jobs = self._jobs()
                    return operation(policy, jobs)
            except ManagerError as error:
                if error.code in {"CONTROLLER_BUSY", "LIVE_DISPATCH_ACTIVE"}:
                    raise
                # Any fail-closed controller decision must also prevent an
                # already-enrolled later job from running while attention is
                # required.  The one-shot audit record itself is retained.
                active = [job for job in jobs if not job.terminal]
                preserved: Job | None = None
                if isinstance(error, PreserveActiveJobError) and len(active) == 1:
                    preserved = active[0]
                else:
                    for active_job in active:
                        with contextlib.suppress(ManagerError):
                            self.services.disarm(active_job)
                self._block(policy, error.code)
                self._save_policy(policy)
                return self._status_from(policy, preserved, time_state="attention")

    def bootstrap_status(self) -> dict[str, Any]:
        def action(policy: dict[str, Any], jobs: list[Job]) -> dict[str, Any]:
            current = self._adopt(policy, jobs)
            self._save_policy(policy)
            try:
                self.services.time_status()
                time_state = "synchronized"
            except ManagerError:
                time_state = "attention"
            return self._status_from(policy, current, time_state=time_state)

        try:
            return self._mutating_operation(action)
        except ManagerError as error:
            if error.code not in {"CONTROLLER_BUSY", "LIVE_DISPATCH_ACTIVE"} or not self.policy_path.is_file():
                raise
            policy = _read_object(self.policy_path, "POLICY_INVALID")
            _validate_policy(policy)
            jobs = self._jobs()
            current = self._ref_job(policy, jobs) if policy["currentJob"] else None
            return self._status_from(policy, current, time_state="unknown")

    def _observe_status_locked(self, policy: dict[str, Any], jobs: list[Job]) -> dict[str, Any]:
        current = self._adopt(policy, jobs)
        try:
            self.services.time_status()
            time_state = "synchronized"
        except ManagerError:
            time_state = "attention"
        snapshot, credits = self._validate_runtime(policy)
        policy["lastSyncAtUtc"] = _utc_text(self.now())
        status = self._status_from(
            policy,
            current,
            time_state=time_state,
            free_reset_expires_at_utc=(_utc_text(credits[0].expires_at) if credits else None),
            automatic_limit_reset_at_utc=self._automatic_limit_reset_at_utc(snapshot),
            primary_used_percent=snapshot.get("primaryUsedPercent"),
            primary_window_duration_mins=snapshot.get("primaryWindowDurationMins"),
            secondary_used_percent=snapshot.get("secondaryUsedPercent"),
            secondary_window_duration_mins=snapshot.get("secondaryWindowDurationMins"),
            secondary_reset_at_utc=snapshot.get("secondaryResetAtUtc"),
            five_hour_used_percent=snapshot.get("fiveHourUsedPercent"),
            five_hour_window_duration_mins=snapshot.get("fiveHourWindowDurationMins"),
            five_hour_reset_at_utc=snapshot.get("fiveHourResetAtUtc"),
            weekly_used_percent=snapshot.get("weeklyUsedPercent"),
            weekly_window_duration_mins=snapshot.get("weeklyWindowDurationMins"),
            weekly_reset_at_utc=snapshot.get("weeklyResetAtUtc"),
            plan_type=snapshot.get("planType"),
        )
        self._save_policy(policy)
        self._log(
            "status",
            state=str(status["automation"]).upper(),
            freeResetExpiresAtUtc=status.get("freeResetExpiresAtUtc"),
            automaticLimitResetAtUtc=status.get("automaticLimitResetAtUtc"),
        )
        return status

    def observe_status(self) -> dict[str, Any]:
        def action(policy: dict[str, Any], jobs: list[Job]) -> dict[str, Any]:
            return self._observe_status_locked(policy, jobs)

        try:
            return self._mutating_operation(action)
        except ManagerError as error:
            if error.code not in {"CONTROLLER_BUSY", "LIVE_DISPATCH_ACTIVE"} or not self.policy_path.is_file():
                raise
            policy = _read_object(self.policy_path, "POLICY_INVALID")
            _validate_policy(policy)
            jobs = self._jobs()
            current = self._ref_job(policy, jobs) if policy["currentJob"] else None
            return self._status_from(policy, current, time_state="unknown")


    def enable(self) -> dict[str, Any]:
        def action(policy: dict[str, Any], jobs: list[Job]) -> dict[str, Any]:
            policy["enabled"] = True
            self._clear_block(policy)
            # ManagerChildOnly validates the on-disk policy before enrolling.
            # Persist consent while controller+dispatch locks still serialize
            # the transition; a later failure is written back as blocked.
            self._save_policy(policy)
            return self._sync_locked(policy, jobs)

        return self._mutating_operation(action)

    def pause(self) -> dict[str, Any]:
        # Pause deliberately does not acquire dispatch.lock. A live guard may
        # own it for the whole T-5 window; guard._disarm first writes the
        # cancellation marker and then performs a non-blocking manifest update.
        with self._controller_lock():
            policy = self._load_policy()
            policy["enabled"] = False
            self._clear_block(policy)
            self._save_policy(policy)
            jobs = self._jobs()
            active = [job for job in jobs if not job.terminal]
            current = self._ref_job(policy, jobs) if policy["currentJob"] else None
            if len(active) > 1:
                self._block(policy, "MULTIPLE_ACTIVE_JOBS")
            cancellation_targets = {job.job_id: job for job in active}
            # During a nothingToReset retry the guard intentionally leaves a
            # crash-safe terminal INDETERMINATE sentinel while it retains the
            # raw ID in memory. Request cancellation for the referenced job
            # even though its persisted state already looks terminal.
            if current is not None:
                cancellation_targets[current.job_id] = current
            for job in cancellation_targets.values():
                self.services.disarm(job)
            if len(active) == 1:
                current = active[0]
                with contextlib.suppress(ManagerError):
                    current = _read_job(active[0].path)
                policy["currentJob"] = self._current_ref(current)
            if current is not None:
                policy["lastResult"] = {
                    "state": current.state if current.terminal else "CANCEL_REQUESTED",
                    "atUtc": _utc_text(self.now()),
                    "expiresAtUtc": _utc_text(current.expires_at),
                    "failureCode": None,
                }
            self._save_policy(policy)
            self._notify_once(
                "paused",
                "Codex Usage Limit Reset Manager",
                "Automatic use has been paused.",
            )
            return self._status_from(policy, current, time_state="unknown")

    def sync(self, *, scheduled: bool = False) -> dict[str, Any]:
        def action(policy: dict[str, Any], jobs: list[Job]) -> dict[str, Any]:
            if not policy["enabled"] and not scheduled:
                return self._observe_status_locked(policy, jobs)
            return self._sync_locked(policy, jobs)

        try:
            return self._mutating_operation(action)
        except ManagerError as error:
            if scheduled and error.code in {"CONTROLLER_BUSY", "LIVE_DISPATCH_ACTIVE"}:
                return self.bootstrap_status()
            raise


    def doctor(self) -> dict[str, Any]:
        issues: list[str] = []
        try:
            status = self.bootstrap_status()
            policy = _read_object(self.policy_path, "POLICY_INVALID")
            _validate_policy(policy)
            jobs = self._jobs()
            active = [job for job in jobs if not job.terminal]
            if len(active) > 1:
                issues.append("MULTIPLE_ACTIVE_JOBS")
            try:
                self.services.time_status()
            except ManagerError as error:
                issues.append(error.code)
            try:
                if getattr(self.services, "supports_approved_cli_cache", False):
                    self.services.validate_cli(
                        policy["accountEmailSha256"], policy.get("approvedCli")
                    )
                else:
                    self.services.validate_cli(policy["accountEmailSha256"])
            except ManagerError as error:
                issues.append(error.code)
            if active:
                try:
                    self.services.validate_task(active[0])
                except ManagerError as error:
                    issues.append(error.code)
            if policy["runtimeInstaller"] is None:
                issues.append("RUNTIME_INSTALLER_NOT_FOUND")
            if policy["runtimeGuard"] is None:
                issues.append("GUARD_RUNTIME_NOT_FOUND")
        except ManagerError as error:
            status = {
                "automation": "attention",
                "enabled": False,
                "reservationStatus": "attention",
                "blockedCode": error.code,
            }
            issues.append(error.code)
        return {"healthy": not issues, "issues": sorted(set(issues)), "status": status}

    @staticmethod
    def _automatic_limit_reset_at_utc(snapshot: Mapping[str, Any]) -> str | None:
        observed_utc = snapshot.get("automaticLimitResetAtUtc")
        if observed_utc is not None:
            if not isinstance(observed_utc, str):
                raise ManagerError("CLI_VALIDATION_FAILED")
            _utc_epoch(observed_utc)
            return observed_utc
        observed_epoch = snapshot.get("automaticLimitResetAt")
        if observed_epoch is None:
            return None
        if type(observed_epoch) is not int or observed_epoch <= 0:
            raise ManagerError("CLI_VALIDATION_FAILED")
        return _utc_text(observed_epoch)

    def _status_from(
        self,
        policy: Mapping[str, Any],
        current: Job | None,
        *,
        time_state: str,
        reservation: str | None = None,
        free_reset_expires_at_utc: str | None = None,
        automatic_limit_reset_at_utc: str | None = None,
        cli_status_override: str | None = None,
        primary_used_percent: float | None = None,
        primary_window_duration_mins: int | None = None,
        secondary_used_percent: float | None = None,
        secondary_window_duration_mins: int | None = None,
        secondary_reset_at_utc: str | None = None,
        five_hour_used_percent: float | None = None,
        five_hour_window_duration_mins: int | None = None,
        five_hour_reset_at_utc: str | None = None,
        weekly_used_percent: float | None = None,
        weekly_window_duration_mins: int | None = None,
        weekly_reset_at_utc: str | None = None,
        plan_type: str | None = None,
    ) -> dict[str, Any]:
        blocked = policy.get("blocked")
        blocked_code = blocked.get("code") if isinstance(blocked, Mapping) else None
        if blocked_code:
            automation = "attention"
        elif policy["enabled"]:
            automation = "on"
        else:
            automation = "paused"
        if reservation is None:
            if blocked_code:
                reservation = "attention"
            elif current is not None and not current.terminal:
                reservation = "scheduled" if current.armed else "preparing"
            elif current is not None:
                reservation = "waiting"
            else:
                reservation = "none"
        approved = policy.get("approvedCli")
        cli_status = "compatible" if isinstance(approved, Mapping) else "pending"
        if blocked_code and blocked_code.startswith(("CLI_", "GUARD_")):
            cli_status = "attention"
        if cli_status_override is not None:
            cli_status = cli_status_override
        return {
            "automation": automation,
            "enabled": bool(policy["enabled"]),
            "nextExpiresAtUtc": _utc_text(current.expires_at) if current and not current.terminal else None,
            "nextProcessAtUtc": _utc_text(current.process_at) if current and not current.terminal else None,
            "freeResetExpiresAtUtc": free_reset_expires_at_utc,
            "automaticLimitResetAtUtc": automatic_limit_reset_at_utc,
            "primaryUsedPercent": primary_used_percent,
            "primaryWindowDurationMins": primary_window_duration_mins,
            "secondaryUsedPercent": secondary_used_percent,
            "secondaryWindowDurationMins": secondary_window_duration_mins,
            "secondaryResetAtUtc": secondary_reset_at_utc,
            "fiveHourUsedPercent": five_hour_used_percent,
            "fiveHourWindowDurationMins": five_hour_window_duration_mins,
            "fiveHourResetAtUtc": five_hour_reset_at_utc,
            "weeklyUsedPercent": weekly_used_percent,
            "weeklyWindowDurationMins": weekly_window_duration_mins,
            "weeklyResetAtUtc": weekly_reset_at_utc,
            "planType": plan_type,
            "cliStatus": cli_status,
            "timeStatus": time_state,
            "lastResult": policy.get("lastResult"),
            "reservationStatus": reservation,
            "blockedCode": blocked_code,
        }


def _local_time(epoch: int) -> str:
    return datetime.fromtimestamp(epoch, UTC).astimezone().strftime("%Y-%m-%d %H:%M:%S")


def _remaining_duration_text(target_epoch: int, *, now: float | None = None) -> str:
    remaining = max(0, target_epoch - int(now if now is not None else time.time()))
    days, remainder = divmod(remaining, 86_400)
    hours, remainder = divmod(remainder, 3_600)
    minutes, _seconds = divmod(remainder, 60)
    parts: list[str] = []
    if days:
        parts.append(f"{days}d")
    if days or hours:
        parts.append(f"{hours}h")
    parts.append(f"{minutes}m")
    return " ".join(parts)


def _status_deadline_text(timestamp_utc: str | None, *, empty: str, now: float | None = None) -> str:
    if not isinstance(timestamp_utc, str):
        return empty
    target_epoch = _utc_epoch(timestamp_utc)
    local_text = _local_time(target_epoch)
    remaining = target_epoch - int(now if now is not None else time.time())
    if remaining <= 0:
        return f"Expired ({local_text})"
    return f"{_remaining_duration_text(target_epoch, now=now)} left ({local_text})"


def _ensure_log_file(path: Path) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        path.write_text("", encoding="utf-8")
    return path


def _open_log_file(path: Path) -> None:
    target = _ensure_log_file(path)
    if os.name == "nt":
        startfile = getattr(os, "startfile", None)
        if callable(startfile):
            startfile(str(target))
            return
        subprocess.Popen(
            ["notepad.exe", str(target)],
            env=_child_process_environment(),
            creationflags=WINDOWLESS_SUBPROCESS_FLAGS,
        )
        return
    opener = shutil.which("xdg-open")
    if opener:
        subprocess.Popen(
            [opener, str(target)],
            env=_child_process_environment(),
            creationflags=WINDOWLESS_SUBPROCESS_FLAGS,
        )
        return
    raise ManagerError("LOG_OPEN_FAILED")



def _system_time_label() -> str:
    return "System time" if sys.platform.startswith("linux") else "Windows time"


ERROR_MESSAGES = {
    "ACCOUNT_CHANGED": "The Codex account has changed.",
    "CLI_VALIDATION_FAILED": "Codex CLI compatibility could not be verified.",
    "TIME_NOT_SYNCHRONIZED": (
        "System time is not synchronized."
        if sys.platform.startswith("linux")
        else "Windows time is not synchronized."
    ),
    "MULTIPLE_ACTIVE_JOBS": "Multiple active jobs were found, so automation stopped safely.",
    "TASK_CONTRACT_INVALID": (
        "The scheduled job configuration has changed."
        if sys.platform.startswith("linux")
        else "The Scheduled Task configuration has changed."
    ),
    "INSUFFICIENT_LEAD_TIME": "There is not enough time left to schedule this reset safely.",
    "LIVE_DISPATCH_ACTIVE": "A usage limit reset is being used now. Try again shortly.",
    "CONTROLLER_BUSY": "Another manager check is already running.",
    "SYSTEMD_UNAVAILABLE": "The systemd user manager is unavailable.",
    "UI_UNAVAILABLE_ON_LINUX": "The manager UI is not available on Linux.",
}


def _human_status(status: Mapping[str, Any]) -> str:
    automation = {"on": "On", "paused": "Paused", "attention": "Needs attention"}.get(
        status.get("automation"), "Needs attention"
    )
    lines = [f"Automatic use: {automation}"]
    h5_pct = status.get("fiveHourUsedPercent")
    if h5_pct is None and (status.get("primaryWindowDurationMins") or 0) <= 720:
        h5_pct = status.get("primaryUsedPercent")
    if isinstance(h5_pct, (int, float)):
        used_v = float(h5_pct)
        rem_v = max(0.0, 100.0 - used_v)
        lines.append(f"5-hour usage: {used_v:.1f}% used ({rem_v:.1f}% left)")
        h5_reset = status.get("fiveHourResetAtUtc")
        if not h5_reset and (status.get("primaryWindowDurationMins") or 0) <= 720:
            h5_reset = status.get("automaticLimitResetAtUtc")
        if h5_reset:
            lines.append(f"5-hour limit reset: {_status_deadline_text(h5_reset, empty='Not available')}")

    wk_pct = status.get("weeklyUsedPercent")
    if wk_pct is None and (status.get("primaryWindowDurationMins") or 0) > 720:
        wk_pct = status.get("primaryUsedPercent")
    elif wk_pct is None and (status.get("secondaryWindowDurationMins") or 0) > 720:
        wk_pct = status.get("secondaryUsedPercent")
    if isinstance(wk_pct, (int, float)):
        used_w = float(wk_pct)
        rem_w = max(0.0, 100.0 - used_w)
        lines.append(f"Weekly usage: {used_w:.1f}% used ({rem_w:.1f}% left)")
        wk_reset = status.get("weeklyResetAtUtc")
        if not wk_reset and (status.get("primaryWindowDurationMins") or 0) > 720:
            wk_reset = status.get("automaticLimitResetAtUtc")
        elif not wk_reset and (status.get("secondaryWindowDurationMins") or 0) > 720:
            wk_reset = status.get("secondaryResetAtUtc")
        if wk_reset:
            lines.append(f"Weekly limit reset: {_status_deadline_text(wk_reset, empty='Not available')}")

    if not isinstance(h5_pct, (int, float)) and not isinstance(wk_pct, (int, float)):
        used_pct = status.get("primaryUsedPercent")
        if isinstance(used_pct, (int, float)):
            used_val = float(used_pct)
            rem_val = max(0.0, 100.0 - used_val)
            dur = status.get("primaryWindowDurationMins")
            dur_str = f" ({dur // 1440}d window)" if dur and dur >= 1440 else (f" ({dur // 60}h window)" if dur else "")
            lines.append(f"Current usage: {used_val:.1f}% used ({rem_val:.1f}% left){dur_str}")
        automatic_limit = status.get("automaticLimitResetAtUtc")
        if automatic_limit is not None or "automaticLimitResetAtUtc" in status:
            lines.append(
                f"Automatic limit reset: {_status_deadline_text(automatic_limit if isinstance(automatic_limit, str) else None, empty='Not available')}"
            )
    free_reset = status.get("freeResetExpiresAtUtc") or status.get("nextExpiresAtUtc")
    if free_reset is not None or "freeResetExpiresAtUtc" in status or "nextExpiresAtUtc" in status:
        lines.append(
            f"Free reset expires: {_status_deadline_text(free_reset if isinstance(free_reset, str) else None, empty='No free reset')}"
        )
    process = status.get("nextProcessAtUtc")
    if isinstance(process, str):
        lines.append(f"Automatic use scheduled: {_local_time(_utc_epoch(process))}")
    cli_text = {
        "compatible": "Compatible",
        "pending": "Not checked",
        "attention": "Needs attention",
    }.get(status.get("cliStatus"), "Needs attention")
    time_text = {
        "synchronized": "Synchronized",
        "unknown": "Not checked",
        "attention": "Needs attention",
    }.get(status.get("timeStatus"), "Needs attention")
    lines.append(f"Codex CLI: {cli_text}")
    lines.append(f"{_system_time_label()}: {time_text}")
    if status.get("blockedCode"):
        lines.append(ERROR_MESSAGES.get(str(status["blockedCode"]), "A safety check needs attention."))
    return "\n".join(lines)


def _console_print(value: str, *, error: bool = False) -> None:
    """Write CLI output when the selected interpreter has a console stream."""
    stream = sys.stderr if error else sys.stdout
    if stream is not None:
        print(value, file=stream)


def _publish_ui_ready(
    state_dir: Path,
    *,
    manager_path: Path | None = None,
    pid: int | None = None,
    now: Callable[[], float] = time.time,
) -> Path:
    """Publish a secret-free marker only after the tray is operational."""
    runtime = (manager_path or Path(__file__)).resolve()
    marker = state_dir / UI_READY_FILENAME
    actual_pid = os.getpid() if pid is None else pid
    if type(actual_pid) is not int or actual_pid <= 0:
        raise ManagerError("UI_READY_PID_INVALID")
    _atomic_json(
        marker,
        {
            "schemaVersion": 1,
            "pid": actual_pid,
            "readyAtUtc": _utc_text(now()),
            "managerSha256": hashlib.sha256(runtime.read_bytes()).hexdigest(),
            "trayReady": True,
        },
    )
    return marker


def run_ui(controller: Controller) -> int:
    if sys.platform.startswith("linux"):
        raise ManagerError("UI_UNAVAILABLE_ON_LINUX")
    if sys.platform.startswith("win"):
        with contextlib.suppress(Exception):
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
                f"OpenAI.Codex.ResetManager.{APP_VERSION}"
            )
    import tkinter as tk
    from tkinter import messagebox, ttk

    lease = UiInstanceLease(controller.state_dir)
    if not lease.acquire():
        return 0

    root: Any = None
    tray: NativeTrayIcon | None = None
    try:
        root = tk.Tk()
        root.title(f"Codex Usage Limit Reset Manager v{APP_VERSION}")
        root.geometry("640x490")
        root.minsize(600, 450)
        root.configure(background="#FFFFFF")
        root.option_add("*Font", ("Segoe UI", 10))

        # Set App Icon
        icon_img: Any = None
        with contextlib.suppress(Exception):
            icon_img = tk.PhotoImage(data=APP_ICON_PNG_64_BASE64)
            root.iconphoto(True, icon_img)
        ico_file = Path(__file__).parent / "assets" / "app_icon.ico"
        if not ico_file.is_file():
            ico_file = Path(os.environ.get("LOCALAPPDATA", "")) / "CodexResetCredit" / "assets" / "app_icon.ico"
        if ico_file.is_file():
            with contextlib.suppress(Exception):
                root.iconbitmap(str(ico_file))

        style = ttk.Style(root)
        style.configure("Manager.TFrame", background="#FFFFFF")
        style.configure(
            "Manager.Title.TLabel",
            background="#FFFFFF",
            foreground="#202124",
            font=("Segoe UI", 18, "bold"),
        )
        style.configure(
            "Manager.Subtitle.TLabel",
            background="#FFFFFF",
            foreground="#4B5563",
            font=("Segoe UI", 10),
        )
        style.configure(
            "Manager.Caption.TLabel",
            background="#FFFFFF",
            foreground="#667085",
            font=("Segoe UI", 10),
        )
        for tone, color in _UI_TONE_COLORS.items():
            style.configure(
                f"Manager.{tone}.Status.TLabel",
                background="#FFFFFF",
                foreground=color,
                font=(
                    "Segoe UI",
                    10,
                    "bold" if tone in {"positive", "info", "warning", "danger"} else "normal",
                ),
            )
        style.configure(
            "Manager.Footer.TLabel",
            background="#FFFFFF",
            foreground="#667085",
            font=("Segoe UI", 9),
        )
        style.configure("Manager.TButton", font=("Segoe UI", 10), padding=(12, 7))

        frame = ttk.Frame(root, padding=(32, 24, 32, 18), style="Manager.TFrame")
        frame.pack(fill="both", expand=True)
        title = ttk.Label(
            frame,
            text=f"Codex Usage Limit Reset Manager  v{APP_VERSION}",
            style="Manager.Title.TLabel",
        )
        title.pack(anchor="w")
        subtitle = ttk.Label(
            frame,
            text=f"Version {APP_VERSION} · Safely uses one selected usage limit reset about five minutes before it expires.",
            style="Manager.Subtitle.TLabel",
            wraplength=520,
        )
        subtitle.pack(anchor="w", pady=(4, 14))

        variables = {
            name: tk.StringVar(value="Checking...")
            for name in (
                "automation",
                "usage",
                "auto_reset",
                "weekly_usage",
                "weekly_reset",
                "free_reset",
                "process",
                "cli",
                "clock",
                "result",
                "reservation",
            )
        }
        labels = (
            ("Automatic use", "automation"),
            ("Current usage", "usage"),
            ("Automatic limit reset", "auto_reset"),
            ("Weekly usage", "weekly_usage"),
            ("Weekly limit reset", "weekly_reset"),
            ("Free reset expires", "free_reset"),
            ("Scheduled use", "process"),
            ("Codex CLI", "cli"),
            (_system_time_label(), "clock"),
            ("Last result", "result"),
            ("Next reservation", "reservation"),
        )
        grid = ttk.Frame(frame, style="Manager.TFrame")
        grid.pack(fill="x")
        value_labels: dict[str, Any] = {}
        for row, (caption, name) in enumerate(labels):
            ttk.Label(
                grid,
                text=caption,
                style="Manager.Caption.TLabel",
            ).grid(
                row=row,
                column=0,
                sticky="w",
                pady=3,
                padx=(0, 28),
            )
            value_label = ttk.Label(
                grid,
                textvariable=variables[name],
                style="Manager.muted.Status.TLabel",
            )
            value_label.grid(
                row=row,
                column=1,
                sticky="w",
                pady=3,
            )
            value_labels[name] = value_label
        grid.columnconfigure(0, minsize=172)
        grid.columnconfigure(1, weight=1)

        buttons = ttk.Frame(frame, style="Manager.TFrame")
        buttons.pack(fill="x", pady=(20, 0))
        toggle = ttk.Button(
            buttons,
            text="Start Automatic Use",
            style="Manager.TButton",
        )
        refresh = ttk.Button(buttons, text="Check Now", style="Manager.TButton")
        doctor_button = ttk.Button(
            buttons,
            text="Troubleshoot",
            style="Manager.TButton",
        )
        open_log_button = ttk.Button(buttons, text="Open Log", style="Manager.TButton")
        toggle.pack(side="left")
        refresh.pack(side="left", padx=10)
        doctor_button.pack(side="left")
        open_log_button.pack(side="left", padx=(10, 0))

        footer = ttk.Label(
            frame,
            text="Automation continues when this window is hidden or exited.",
            style="Manager.Footer.TLabel",
        )
        footer.pack(anchor="w", pady=(14, 0))
        busy = tk.BooleanVar(value=False)
        events: queue.Queue[tuple[str, Any]] = queue.Queue()
        tray_events: queue.Queue[str] = queue.Queue()
        latest: dict[str, Any] = {"enabled": False}
        closing = {"requested": False, "destroyed": False}

        def present(status: Mapping[str, Any]) -> None:
            latest.clear()
            latest.update(status)
            variables["automation"].set(
                {"on": "On", "paused": "Paused", "attention": "Needs attention"}.get(
                    status.get("automation"), "Needs attention"
                )
            )

            # Short-term / 5-hour usage & reset (Current usage & Automatic limit reset)
            h5_pct = status.get("fiveHourUsedPercent")
            if h5_pct is None and (status.get("primaryWindowDurationMins") or 0) <= 720:
                h5_pct = status.get("primaryUsedPercent")
            h5_dur = status.get("fiveHourWindowDurationMins") or status.get("primaryWindowDurationMins")
            if isinstance(h5_pct, (int, float)):
                used_v = float(h5_pct)
                rem_v = max(0.0, 100.0 - used_v)
                dur_tag = f" ({h5_dur // 60}h window)" if h5_dur else " (5h window)"
                variables["usage"].set(f"{used_v:.1f}% used ({rem_v:.1f}% left){dur_tag}")
            else:
                used_pct = status.get("primaryUsedPercent")
                if isinstance(used_pct, (int, float)):
                    used_val = float(used_pct)
                    rem_val = max(0.0, 100.0 - used_val)
                    dur = status.get("primaryWindowDurationMins")
                    dur_str = f" ({dur // 1440}d window)" if dur and dur >= 1440 else (f" ({dur // 60}h window)" if dur else "")
                    variables["usage"].set(f"{used_val:.1f}% used ({rem_val:.1f}% left){dur_str}")
                else:
                    variables["usage"].set("Not active")

            h5_reset = status.get("fiveHourResetAtUtc")
            if not h5_reset and (status.get("primaryWindowDurationMins") or 0) <= 720:
                h5_reset = status.get("automaticLimitResetAtUtc")
            fallback_reset = status.get("automaticLimitResetAtUtc") if isinstance(status.get("automaticLimitResetAtUtc"), str) else None
            variables["auto_reset"].set(
                _status_deadline_text(h5_reset if isinstance(h5_reset, str) else fallback_reset, empty="Not available")
            )

            # Weekly usage & reset
            wk_pct = status.get("weeklyUsedPercent")
            if wk_pct is None and (status.get("primaryWindowDurationMins") or 0) > 720:
                wk_pct = status.get("primaryUsedPercent")
            elif wk_pct is None and (status.get("secondaryWindowDurationMins") or 0) > 720:
                wk_pct = status.get("secondaryUsedPercent")
            wk_dur = status.get("weeklyWindowDurationMins")
            if isinstance(wk_pct, (int, float)):
                used_w = float(wk_pct)
                rem_w = max(0.0, 100.0 - used_w)
                dur_w_tag = f" ({wk_dur // 1440}d window)" if wk_dur and wk_dur >= 1440 else " (7d window)"
                variables["weekly_usage"].set(f"{used_w:.1f}% used ({rem_w:.1f}% left){dur_w_tag}")
            else:
                variables["weekly_usage"].set("Not active")

            wk_reset = status.get("weeklyResetAtUtc")
            if not wk_reset and (status.get("primaryWindowDurationMins") or 0) > 720:
                wk_reset = status.get("automaticLimitResetAtUtc")
            elif not wk_reset and (status.get("secondaryWindowDurationMins") or 0) > 720:
                wk_reset = status.get("secondaryResetAtUtc")
            variables["weekly_reset"].set(
                _status_deadline_text(wk_reset if isinstance(wk_reset, str) else None, empty="Not available")
                if wk_reset else "Not active"
            )
            free_reset_utc = status.get("freeResetExpiresAtUtc") or status.get("nextExpiresAtUtc")
            variables["free_reset"].set(
                _status_deadline_text(
                    free_reset_utc if isinstance(free_reset_utc, str) else None,
                    empty="No free reset",
                )
            )
            variables["process"].set(
                _local_time(_utc_epoch(status["nextProcessAtUtc"]))
                if status.get("nextProcessAtUtc")
                else "No reservation"
            )
            variables["cli"].set(
                {
                    "compatible": "Compatible",
                    "pending": "Not checked",
                    "attention": "Needs attention",
                }.get(status.get("cliStatus"), "Needs attention")
            )
            variables["clock"].set(
                {
                    "synchronized": "Synchronized",
                    "unknown": "Not checked",
                    "attention": "Needs attention",
                }.get(status.get("timeStatus"), "Needs attention")
            )
            last = status.get("lastResult")
            variables["result"].set(
                str(last.get("state")) if isinstance(last, Mapping) else "No history"
            )
            variables["reservation"].set(
                {
                    "scheduled": "Scheduled",
                    "preparing": "Preparing",
                    "waiting": "Waiting safely",
                    "none": "No reservation",
                    "attention": "Needs attention",
                }.get(status.get("reservationStatus"), "Needs attention")
            )
            for name, label in value_labels.items():
                label.configure(
                    style=f"Manager.{_ui_tone_for_text(variables[name].get())}.Status.TLabel"
                )
            toggle.configure(
                text="Pause Automatic Use" if status.get("enabled") else "Start Automatic Use"
            )

        def worker(kind: str) -> None:
            try:
                if kind == "enable":
                    result = controller.enable()
                elif kind == "pause":
                    result = controller.pause()
                elif kind == "sync":
                    result = controller.sync()
                elif kind == "doctor":
                    result = controller.doctor()
                else:
                    result = controller.observe_status()
                events.put((kind, result))
            except Exception as error:
                code = error.code if isinstance(error, ManagerError) else "UNEXPECTED_ERROR"
                try:
                    observed = controller.observe_status()
                except Exception:
                    observed = None
                events.put(("error", (code, observed)))

        def start(kind: str) -> None:
            if busy.get() or closing["requested"]:
                return
            busy.set(True)
            for button in (toggle, refresh, doctor_button):
                button.state(["disabled"])
            threading.Thread(target=worker, args=(kind,), daemon=True).start()

        def open_log() -> None:
            try:
                _open_log_file(controller.log_path)
            except Exception:
                messagebox.showerror(
                    "Open Log Failed",
                    f"The manager log could not be opened.\n\nPath:\n{controller.log_path}",
                )


        def restore_window() -> None:
            if closing["destroyed"]:
                return
            root.deiconify()
            with contextlib.suppress(tk.TclError):
                if root.state() == "iconic":
                    root.state("normal")
            root.lift()
            root.after_idle(root.focus_force)

        def shutdown_ui() -> None:
            if closing["destroyed"]:
                return
            closing["destroyed"] = True
            lease.clear_ready()
            if tray is not None:
                tray.stop()
            with contextlib.suppress(tk.TclError):
                root.destroy()

        def request_exit() -> None:
            closing["requested"] = True
            with contextlib.suppress(tk.TclError):
                root.withdraw()
            if not busy.get():
                shutdown_ui()

        def hide_to_tray() -> None:
            if tray is not None and tray.running:
                root.withdraw()
            else:
                # Never leave an invisible UI behind if Explorer rejected the
                # tray icon. Automation itself remains independent of this UI.
                shutdown_ui()

        def poll_results() -> None:
            try:
                kind, value = events.get_nowait()
            except queue.Empty:
                if not closing["destroyed"]:
                    root.after(100, poll_results)
                return
            busy.set(False)
            if not closing["requested"]:
                for button in (toggle, refresh, doctor_button):
                    button.state(["!disabled"])
            if kind == "error":
                code, observed = value if isinstance(value, tuple) else (value, None)
                if observed is not None and not closing["requested"]:
                    present(observed)
                if not closing["requested"]:
                    messagebox.showerror(
                        "Needs Attention",
                        ERROR_MESSAGES.get(
                            str(code),
                            "A problem occurred while running the safety checks.",
                        ),
                    )
            elif kind == "doctor":
                report = value
                if not closing["requested"]:
                    if report["healthy"]:
                        messagebox.showinfo(
                            "Troubleshoot and Logs",
                            f"All safety checks passed.\n\nLog file:\n{controller.log_path}",
                        )
                    else:
                        rendered = "\n".join(
                            ERROR_MESSAGES.get(code, code) for code in report["issues"]
                        )
                        messagebox.showwarning(
                            "Troubleshoot and Logs",
                            f"{rendered}\n\nLog file:\n{controller.log_path}",
                        )
                    present(report["status"])
            elif not closing["requested"]:
                present(value)
            if closing["requested"]:
                shutdown_ui()
            elif not closing["destroyed"]:
                root.after(100, poll_results)

        def poll_tray_events() -> None:
            if lease.ready_published and (tray is None or not tray.running):
                lease.clear_ready()
                restore_window()
            while True:
                try:
                    action = tray_events.get_nowait()
                except queue.Empty:
                    break
                if action == "open":
                    restore_window()
                elif action == "check":
                    start("check")
                elif action == "toggle":
                    start("pause" if latest.get("enabled") else "enable")
                elif action == "exit":
                    request_exit()
            if not closing["destroyed"]:
                root.after(100, poll_tray_events)

        def poll_show_request() -> None:
            if lease.consume_show_request():
                restore_window()
            if not closing["destroyed"]:
                root.after(250, poll_show_request)

        toggle.configure(
            command=lambda: start("pause" if latest.get("enabled") else "enable")
        )
        refresh.configure(command=lambda: start("check"))
        doctor_button.configure(command=lambda: start("doctor"))
        open_log_button.configure(command=open_log)
        tray = NativeTrayIcon(
            on_open=lambda: tray_events.put("open"),
            on_check=lambda: tray_events.put("check"),
            on_toggle=lambda: tray_events.put("toggle"),
            on_exit=lambda: tray_events.put("exit"),
            is_enabled=lambda: bool(latest.get("enabled")),
        )
        if tray.start():
            try:
                lease.publish_ready(Path(__file__).resolve())
            except ManagerError:
                # If the handshake cannot be recorded, keep the manager
                # visible and do not offer a tray-only close path.
                tray.stop()
                tray = None
        root.protocol("WM_DELETE_WINDOW", hide_to_tray)
        root.after(100, poll_results)
        root.after(100, poll_tray_events)
        root.after(250, poll_show_request)
        root.after(100, lambda: start("status"))
        root.mainloop()
        return 0
    finally:
        if tray is not None:
            tray.stop()
        if root is not None:
            with contextlib.suppress(Exception):
                root.destroy()
        lease.release()


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Manage automatic use of Codex usage limit resets")
    parser.add_argument("--version", action="version", version=f"%(prog)s {APP_VERSION}")
    parser.add_argument("--root", type=Path, help=argparse.SUPPRESS)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("ui", help="open the manager interface when available")
    commands.add_parser("enable", help="enable continuous automatic scheduling")
    commands.add_parser("pause", help="pause automation and cancel the active one-shot")
    sync = commands.add_parser("sync", help="check health and reconcile the next one-shot")
    sync.add_argument("--scheduled", action="store_true", help=argparse.SUPPRESS)
    status = commands.add_parser("status", help="show sanitized automatic-use status")
    status.add_argument("--json", action="store_true")
    commands.add_parser("doctor", help="run safety diagnostics and refresh sanitized status")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    try:
        controller = Controller((args.root or _default_root()).resolve())
        if args.command == "ui":
            return run_ui(controller)
        if args.command == "enable":
            result = controller.enable()
        elif args.command == "pause":
            result = controller.pause()
        elif args.command == "sync":
            result = controller.sync(scheduled=args.scheduled)
        elif args.command == "status":
            result = controller.observe_status()
        elif args.command == "doctor":
            report = controller.doctor()
            _console_print(
                "All safety checks passed."
                if report["healthy"]
                else "One or more safety checks need attention."
            )
            for issue in report["issues"]:
                _console_print(f"- {ERROR_MESSAGES.get(issue, issue)}")
            return 0 if report["healthy"] else 1
        else:
            raise ManagerError("UNKNOWN_COMMAND")
        if args.command == "status" and args.json:
            _console_print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
        else:
            _console_print(_human_status(result))
        return 0 if result.get("automation") != "attention" else 1
    except ManagerError as error:
        _console_print(f"error: {error.code}", error=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

