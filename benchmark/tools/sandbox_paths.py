"""Path helpers shared by the offline compiler launcher."""
from pathlib import Path


def _below(root: Path, path: Path) -> Path:
    root = root.resolve()
    path = path.resolve()
    try:
        path.relative_to(root)
    except ValueError as error:
        raise ValueError(f"path must stay below workspace {root}: {path}") from error
    return path


def _bind(command: list[str], source: Path, destination: str, *, writable: bool) -> None:
    source = source.resolve()
    if not source.exists():
        raise RuntimeError(f"required bind source does not exist: {source}")
    command.extend(("--bind" if writable else "--ro-bind", str(source), destination))
