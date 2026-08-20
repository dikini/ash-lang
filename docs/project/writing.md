# Writing guide

These rules apply to repository prose and agent communication, including chat.

Write to reduce uncertainty.

- Prefer plain, direct language and active voice.
- Remove words that add no information.
- Label facts, accepted decisions, proposals, and ideas by their actual status.
- Keep explanation proportional to how firmly the project has committed.
- Use technical terms when they name stable concepts; avoid unnecessary jargon.
- Avoid architecture-by-adjective. State the concrete property instead of calling something “extensible,” “robust,” “modular,” or “scalable.”
- Prefer nouns and verbs over adjectives.
- Explain enough to support the decision or task, then stop.
- Do not design mechanisms or requirements for hypothetical needs.

For example, replace “Core is extensible” with “Adding an effect family does not require a new recursive Core expression form.” The second sentence names a property that design and implementation can test.

## Formal notation

Follow the [formal-notation guide](notation.md) for grammar productions and
Gentzen-style inference rules. Use `ebnf` fences for grammar productions and
`sequent` fences for inference rules with premises and one conclusion. Explain
every formal-notation fence in prose and keep the explanation consistent with
the notation. Use ordinary prose or inline notation when no production or
inference structure is needed.
