"""Adversarial visibility probe executed inside the proposer sandbox."""

from __future__ import annotations

import json
import os
import pathlib
import socket
import sys


catalog_path = pathlib.Path(sys.argv[1])
output_dir = pathlib.Path(sys.argv[2])
catalog = json.loads(catalog_path.read_text())
forbidden_keys = {"proof", "proof_body", "value", "evidence", "checker_command"}
assert catalog["proof_bodies_included"] is False
assert all(not forbidden_keys.intersection(entry) for entry in catalog["entries"])

repository_candidates = [
    pathlib.Path("/home/mjbommar/projects/personal/axeyum"),
    pathlib.Path("/repo"),
    pathlib.Path("/nas3/data"),
    pathlib.Path("/data0"),
    pathlib.Path("/proc/1/root/home/mjbommar/projects/personal/axeyum"),
]
repository_visible = any(path.exists() for path in repository_candidates)

network = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
network.settimeout(0.2)
network_reachable = network.connect_ex(("1.1.1.1", 53)) == 0
network.close()

assert not repository_visible
assert not network_reachable
unexpected_environment = sorted(
    set(os.environ).difference({"HOME", "PATH", "PWD", "LC_CTYPE"})
)
assert not unexpected_environment
assert os.environ["HOME"] == "/nonexistent"
assert os.environ["PATH"] == "/usr/bin"
(output_dir / "probe-result.json").write_text(
    json.dumps(
        {
            "catalog_sha256": catalog["catalog_sha256"],
            "environment_sanitized": True,
            "network_reachable": network_reachable,
            "repository_visible": repository_visible,
            "visible_entries": len(catalog["entries"]),
        },
        indent=2,
        sort_keys=True,
    )
    + "\n"
)
