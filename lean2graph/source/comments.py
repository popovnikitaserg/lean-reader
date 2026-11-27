from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Comment:
    text: str
    start_line: int
    start_column: int
    end_line: int
    end_column: int


def tokenize_comments(source: str) -> list[Comment]:
    comments: list[Comment] = []
    i = 0
    line = 1
    column = 1
    length = len(source)

    def advance(text: str) -> None:
        nonlocal line, column
        for char in text:
            if char == "\n":
                line += 1
                column = 1
            else:
                column += 1

    while i < length:
        char = source[i]
        if char == '"':
            i += 1
            advance('"')
            while i < length:
                if source[i] == "\\" and i + 1 < length:
                    pair = source[i : i + 2]
                    advance(pair)
                    i += 2
                elif source[i] == '"':
                    advance('"')
                    i += 1
                    break
                else:
                    advance(source[i])
                    i += 1
            continue
        if source.startswith("--", i):
            start_line, start_column = line, column
            end = source.find("\n", i)
            if end == -1:
                end = length
            text = source[i:end].strip()
            advance(source[i:end])
            i = end
            comments.append(
                Comment(text, start_line, start_column, line, column)
            )
            continue
        if source.startswith("/-", i):
            start_line, start_column = line, column
            i += 2
            advance("/-")
            depth = 1
            text_parts: list[str] = ["/-"]
            while i < length and depth:
                if source.startswith("/-", i):
                    text_parts.append("/-")
                    advance("/-")
                    i += 2
                    depth += 1
                elif source.startswith("-/", i):
                    text_parts.append("-/")
                    advance("-/")
                    i += 2
                    depth -= 1
                else:
                    text_parts.append(source[i])
                    advance(source[i])
                    i += 1
            comments.append(
                Comment(
                    "".join(text_parts),
                    start_line,
                    start_column,
                    line,
                    column,
                )
            )
            continue
        advance(char)
        i += 1
    return comments
