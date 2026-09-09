# Flex contract checker fixtures

These fixtures are derived from the Flex contracts repository:

- Repository: https://github.com/flexmeow/flex-contracts
- Revision: `ac0835f47e8cf7a3b3e7db2dbe3ac5cbebd5148d`
- License: GNU Affero General Public License v3.0; see `LICENSE`

## Daddy

Original source: `src/periphery/daddy.vy`

The copied source was upgraded from Vyper 0.4.3 to the prerelease version used
by this repository:

```sh
vyupgrade \
  --source-version 0.4.3 \
  --target-version 0.5.0a3 \
  --target-vyper "$(command -v vyper)" \
  --write daddy/daddy.vy
```

`vyupgrade` reported unchanged ABI, method IDs, and storage layout. The original
source SHA-256 was
`8c1c34a37fdaf7eb0c24d53993aac55e7be64f695ac2c5723c724fa0911f39e8`;
the upgraded source SHA-256 is
`53338f17a5cae4f6152d4dd1c629180372b79016ed24314b94528d99255fdc2a`.

Compiler output was generated using the exact compiler revision in the
repository's `VYPER_PIN`:

```sh
cd daddy
vyper -f annotated_ast,layout daddy.vy > compiler-output.jsonl
```

The two output objects were merged into `daddy.json`. Absolute paths beneath
the fixture directory were replaced recursively with the stable prefix
`third_party/flex/daddy/`; generation fails if the result still contains the
local fixture root, `/home/`, `/tmp/`, or the generating username. The raw
JSONL is intermediate output and is not retained.

At generation time this was Vyper
`0.5.0a3+commit.1d81b8731` (`1d81b8731a1f4d0fff953212deba5941c89602eb`).
