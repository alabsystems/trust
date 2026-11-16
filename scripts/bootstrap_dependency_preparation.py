"""Typed DATA for a future authenticated resident dependency-preparation route.

This module never executes a fetch or constructs source/cache/SDK ownership.
The actual resident must retain those owners, authenticate the submission and
judge its original endpoint before consuming this request. There is no CLI,
JSON importer, availability receipt or raw-process fallback here.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from types import MappingProxyType

HERE = Path(__file__).resolve().parent
archives = __trust_source_loader__.module('trust_preparation_archives', HERE / 'seed_input_archives.py')
dependencies = archives.dependencies
records = archives.records


class FetchPass(Enum):
    CALLER_NETWORK_POLICY = 'caller-network-policy'
    OFFLINE = 'offline'


class RequestKind(Enum):
    PREPARE_THEN_CHECK = 'prepare-then-check'
    OFFLINE_CHECK = 'offline-check'


def _endpoint(deadline, views):
    # No duration/default is accepted and no endpoint is renewed between roots
    # or passes. A partly consumed original budget may have less than 5s left.
    records.remaining(deadline)
    import time
    records.require(deadline - time.monotonic() <= dependencies.DEFAULT_BUDGET_SECONDS,
                    'preparation endpoint exceeds the complete original budget')
    for view in views:
        records.require(type(view) is archives._CommittedSourceView,
                        'preparation needs the existing committed source view')
        records.require(type(view.end) in (int, float) and view.end == deadline,
                        'preparation source view has a different original endpoint')
        records.require(view.root.resolve(strict=True) == view.root and not view.root.is_symlink(),
                        'preparation source root is not canonical')


def _implementation_inputs(orchestration):
    loader = __trust_source_loader__
    # Use the source filename of the actual loader method, including when its
    # bootstrap module was executed directly rather than installed in sys.modules.
    loader_path = Path(type(loader).module.__code__.co_filename)
    records.require(loader_path == HERE / 'seed_custody_source.py'
                    and loader.root == orchestration.root == HERE.parent,
                    'preparation needs the original bound source loader')
    paths = {Path(__file__), loader_path}
    paths.update(Path(name) if Path(name).is_absolute() else loader.root / name
                 for name in loader.executed)
    return paths


def _selection(source, orchestration, targo, environment, deadline):
    _endpoint(deadline, (source, orchestration))
    records.require(type(targo) is str and targo and '\x00' not in targo,
                    'configured bootstrap Targo path is missing or invalid')
    # Keep the configured spelling separately. Path anchoring uses the same
    # invocation root as dependency_closure, never PATH or executable discovery.
    driver = Path(targo)
    if not driver.is_absolute():
        driver = source.root / driver
    records.require(driver.is_file(), 'configured bootstrap Targo is missing: ' + targo)
    for relative in (*dependencies._RECIPE_INPUTS, *dependencies._BASE_MANIFESTS):
        records.require(source.is_file(source.root / relative),
                        'required committed bootstrap authority is missing: ' + relative)
    manifests = tuple(dependencies.stage0_bootstrap_manifest_roots(source.root, source_view=source))
    records.require(manifests, 'bootstrap recipe manifest envelope is empty')
    inputs = set(dependencies._source_inputs(
        source.root, list(manifests), dict(environment), source_view=source,
        graph_source_view=orchestration, require_lockfiles=True))
    implementation = _implementation_inputs(orchestration)
    for path in implementation:
        records.require(path.is_relative_to(orchestration.root) and orchestration.is_file(path),
                        'preparation implementation is not in committed source: ' + str(path))
    # Reuse the existing view's byte/link checks for every selected committed
    # input, including locks. Prospective absent configs remain in the read-set;
    # an unrecorded config/lock cannot silently become a different Cargo input.
    for path in sorted(inputs | implementation):
        orchestration_input = (path in implementation
                               or path == orchestration.root / 'scripts/recreate_bootstrap.py')
        view = orchestration if orchestration_input else source
        if path.is_relative_to(view.root):
            if view.is_file(path):
                view.read_text(path)
            else:
                view.require_absent(path)
    read_set = inputs | implementation | {driver, driver.resolve(strict=True)}
    _endpoint(deadline, (source, orchestration))
    return driver, manifests, tuple(sorted(inputs)), tuple(sorted(read_set))


@dataclass(frozen=True, slots=True)
class DependencyPreparationRequest:
    """Complete recipe request DATA, never a source lock or native capability.

    No argv field or deserializer can turn observations into an execution
    owner. A future distinct authenticated resident route must supply that
    owner and preserve this request's original source/seed/control SDK roles.
    """
    root: Path
    configured_targo: str
    targo_path: Path
    manifests: tuple[Path, ...]
    source_inputs: tuple[Path, ...]
    read_set: tuple[Path, ...]
    deadline: float
    kind: RequestKind
    environment: tuple[tuple[str, str], ...] = field(repr=False)
    _source: object = field(repr=False, compare=False)
    _orchestration: object = field(repr=False, compare=False)

    @property
    def glob_input_paths(self):
        """Actual maintained evaluator reach DATA for the same native snapshot.

        This selects no directory owner and proves no physical membership.
        The factory captures these paths and reruns the SAME selector.
        """
        return tuple(sorted(self._source._glob_inputs | self._orchestration._glob_inputs))

    @property
    def unowned_input_paths(self):
        """Explicit native factory gaps, never successful physical custody.

        Source selection can describe external config/program paths but cannot
        borrow their owners. A captured view covers only its actual read map.
        """
        missing = (set(self.read_set) if self._source._captured_reads is None else
                   {path for path in self.read_set if not path.is_relative_to(self.root)
                    or path.relative_to(self.root).as_posix() not in self._source._captured_reads})
        for view in (self._source, self._orchestration):
            missing.update(path for path in view._glob_inputs
                           if path.relative_to(view.root).as_posix() not in view._captured_listings)
            missing.update(path for path in view._resolution_inputs
                           if view._captured_reads is None or
                           path.relative_to(view.root).as_posix() not in view._captured_reads)
        return tuple(sorted(missing))

    @property
    def passes(self) -> tuple[FetchPass, ...]:
        if self.kind is RequestKind.OFFLINE_CHECK:
            return (FetchPass.OFFLINE,)
        records.require(self.kind is RequestKind.PREPARE_THEN_CHECK,
                        'unknown dependency preparation request kind')
        return (FetchPass.CALLER_NETWORK_POLICY, FetchPass.OFFLINE)

    def environment_for(self, phase: FetchPass):
        records.require(type(phase) is FetchPass and phase in self.passes,
                        'unknown dependency preparation pass')
        environment = dict(self.environment)
        if phase is FetchPass.OFFLINE:
            environment['CARGO_NET_OFFLINE'] = 'true'
        return MappingProxyType(environment)

    def recheck_selection(self) -> None:
        """Re-read the same source selection without renewing its endpoint.

        This supplies no config/cache/SDK lifetime custody or successful fetch
        observation. In particular it cannot enable the existing Darwin _fetch.
        """
        selected = _selection(self._source, self._orchestration, self.configured_targo,
                              self.environment, self.deadline)
        records.require(type(self.kind) is RequestKind, 'unknown dependency preparation request kind')
        records.require(self.root == self._source.root and selected == (
            self.targo_path, self.manifests, self.source_inputs, self.read_set),
            'dependency preparation selection changed')


def preparation_request(source, orchestration, targo: str, environment: dict[str, str], *,
                        deadline: float) -> DependencyPreparationRequest:
    """Describe EVERY maintained recipe root, followed by the offline pass.

    The two existing committed views are read-only observations, not source
    ownership. Their original endpoint is mandatory. Neither root/argv lists
    nor serialized view/hash assertions are accepted in their place.
    """
    return _request(source, orchestration, targo, environment, deadline,
                    RequestKind.PREPARE_THEN_CHECK)


def offline_check_request(source, orchestration, targo: str, environment: dict[str, str], *,
                          deadline: float) -> DependencyPreparationRequest:
    """Describe the same complete envelope with ONLY locked offline fetches.

    This distinct request cannot be consumed as caller-policy preparation.
    It neither runs Cargo nor establishes that the offline inputs are present.
    """
    return _request(source, orchestration, targo, environment, deadline, RequestKind.OFFLINE_CHECK)


def _request(source, orchestration, targo, environment, deadline, kind):
    records.require(type(environment) is dict and all(
        type(key) is str and key and '=' not in key and '\x00' not in key
        and type(value) is str and '\x00' not in value
        for key, value in environment.items()), 'invalid original preparation environment')
    copied = tuple(sorted(environment.items()))
    driver, manifests, inputs, read_set = _selection(source, orchestration, targo, copied, deadline)
    return DependencyPreparationRequest(source.root, targo, driver, manifests, inputs, read_set,
                                        deadline, kind, copied, source, orchestration)
