#!/usr/bin/env python3
"""Install the repository-pinned Rocq Prover in an isolated opam switch.

Purpose:
    Provide a reproducible, paste-safe installation program for Debian 13
    that does not alter the user's existing opam default switch or their
    specialized icar16-colibri2 switch.

Prerequisites:
    An initialized opam installation, OCaml build prerequisites, Python 3,
    and Deal 4.24.6. The Rocq compiler is built from source using opam.

Safety:
    All external commands use subprocess.run with argument sequences,
    never a shell. Every opam operation capable of changing installed
    packages is scoped to the dedicated rocq-9.2 switch. Re-running
    skips creation of the existing switch and repository registration.

Limits:
    The Deal contracts check the command plan and input domains, not the
    correctness of opam, the network, downloaded source packages, or the
    Rocq kernel. A successful installation must still pass rocq --version
    and subsequent project proof compilation.

AI disclosure:
    This utility was drafted with AI assistance and requires independent
    review before deployment to security-sensitive systems.
"""

from __future__ import annotations

import argparse
import shlex
import shutil
import subprocess
import sys

import deal

SWITCH = "rocq-9.2"
SWITCH_OPTION = "--switch=" + SWITCH
OCAML_COMPILER = "ocaml-base-compiler.4.14.2"
RELEASE_REPOSITORY = "https://rocq-prover.org/opam/released"
ROCQ_CORE = "rocq-core=9.2.0"
REPO_NAME = "rocq-released"


@deal.pre(lambda switch_exists, repository_exists: isinstance(switch_exists, bool))
@deal.pre(lambda switch_exists, repository_exists: isinstance(repository_exists, bool))
@deal.pure
@deal.post(lambda result: isinstance(result, tuple))
@deal.post(lambda result: all(isinstance(command, tuple) and bool(command) for command in result))
@deal.post(lambda result: all(all(isinstance(token, str) and bool(token) for token in command)
                               for command in result))
@deal.post(lambda result: all(command[0] == "opam" for command in result))
@deal.post(lambda result: result[0] == ("opam", "update", "--yes"))
@deal.post(lambda result: result[-3] == ("opam", "update", SWITCH_OPTION, "--yes"))
@deal.post(lambda result: result[-2] == ("opam", "install", SWITCH_OPTION, "--yes",
                                           "rocq-prover", ROCQ_CORE))
@deal.post(lambda result: result[-1] == ("opam", "exec", SWITCH_OPTION, "--", "rocq", "--version"))
@deal.post(lambda result: len(set(result)) == len(result))
@deal.post(lambda result: all("sudo" not in command and "--global" not in command
                               for command in result))
@deal.ensure(lambda switch_exists, repository_exists, result:
             (("opam", "switch", "create", SWITCH, OCAML_COMPILER, "--yes") in result)
             is (not switch_exists))
@deal.ensure(lambda switch_exists, repository_exists, result:
             (("opam", "repository", "add", REPO_NAME, RELEASE_REPOSITORY,
               SWITCH_OPTION, "--yes") in result) is (not repository_exists))
@deal.ensure(lambda switch_exists, repository_exists, result:
             len(result) == 4 + (not switch_exists) + (not repository_exists))
@deal.post(lambda result: all(command[0:2] == ("opam", "switch") or
                               command == ("opam", "update", "--yes") or
                               SWITCH_OPTION in command for command in result))
def installation_plan(
    switch_exists: bool, repository_exists: bool
) -> tuple[tuple[str, ...], ...]:
    """Construct an idempotent and switch-scoped opam command plan.

    Both flags report the state of the named target switch. When a switch
    is absent, repository registration is necessarily treated as absent.
    A global metadata refresh precedes switch creation, while repository
    registration precedes the switch-local refresh and package installation.

    Contract groups cover input types, purity, output structure, nonempty
    tokens, exact pinned commands, optional steps, sequence size, command
    uniqueness, and explicit isolation from the global opam environment.
    """
    commands: list[tuple[str, ...]] = [("opam", "update", "--yes")]
    if not switch_exists:
        commands.append(("opam", "switch", "create", SWITCH, OCAML_COMPILER, "--yes"))
    if not repository_exists:
        commands.append(("opam", "repository", "add", REPO_NAME,
                         RELEASE_REPOSITORY, SWITCH_OPTION, "--yes"))
    commands.extend((
        ("opam", "update", SWITCH_OPTION, "--yes"),
        ("opam", "install", SWITCH_OPTION, "--yes", "rocq-prover", ROCQ_CORE),
        ("opam", "exec", SWITCH_OPTION, "--", "rocq", "--version"),
    ))
    return tuple(commands)


if __name__ == "__main__":
    # Contracts are enabled even when Python is invoked with -O.
    deal.enable(warn=False)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true",
                        help="show installation commands without executing or probing opam")
    args = parser.parse_args()

    try:
        if args.dry_run:
            # Conservative first-install preview: both optional commands are shown.
            commands = installation_plan(False, False)
        else:
            if shutil.which("opam") is None:
                parser.error("opam is missing; install it via 'sudo apt install opam'")
            switches = subprocess.run(
                ("opam", "switch", "list", "--short"), capture_output=True,
                text=True, check=True,
            ).stdout.splitlines()
            switch_present = SWITCH in (line.strip() for line in switches)
            if switch_present:
                repositories = subprocess.run(
                    ("opam", "repository", "list", "--short", SWITCH_OPTION),
                    capture_output=True, text=True, check=True,
                ).stdout.splitlines()
                repository_present = REPO_NAME in (line.strip() for line in repositories)
            else:
                repository_present = False
            commands = installation_plan(switch_present, repository_present)
        for command in commands:
            print(shlex.join(command), flush=True)
            if not args.dry_run:
                subprocess.run(command, check=True)
    except subprocess.CalledProcessError as error:
        print("Installation stopped: command failed with status " +
              str(error.returncode) + ": " + shlex.join(error.cmd), file=sys.stderr)
        raise SystemExit(error.returncode) from error
