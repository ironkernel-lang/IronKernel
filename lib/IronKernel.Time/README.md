# IronKernel.Time

Dates, durations, and formatting for IronKernel over `System.DateTime` and
`System.TimeSpan`, with one discipline applied throughout: **instants are
UTC**. Constructors build UTC instants, `now` is UTC, parsing assumes and
adjusts to UTC, and crossing into local time only happens through the two
conversions that say so by name.

```scheme
(date 2024 3 15)                     ; midnight UTC
(+ (now) (hours 2))                  ; the tower already adds durations
(- deadline (now))                   ; ... and subtracts to a duration
(date->string (date 2024 3 15))      ; "2024-03-15T00:00:00.0000000Z"
(date->unix (date 2024 3 15))        ; 1710460800
```

The runtime's arithmetic accepts these values directly: `date + duration`
(either order), `duration + duration`, `date - date`, `date - duration`, and
`duration - duration` are ordinary `+` and `-`. This package supplies what the
tower does not — construction, accessors, ordering, calendar arithmetic,
conversion, and invariant-culture formatting and parsing. Parsers return `#f`
on malformed input, following `IronKernel.Strings`' discipline.

## Use

```bash
ik add IronKernel.Time 0.1.0
```

Or, from a checkout of this repository:

```bash
cd lib/IronKernel.Test && ik pack     # seed the local feed for the test DSL
cd ../IronKernel.Time
ik test
ik pack
```

## API

### Construction

| Form | Meaning |
|---|---|
| `(now)` | The current instant, UTC. |
| `(today)` | Now's calendar day at midnight UTC. |
| `(date y m d)` | Midnight UTC on that day. An impossible day signals. |
| `(date-time y m d h mi s [ms])` | A UTC instant. |
| `(date? x)` / `(duration? x)` / `(date-utc? t)` | |

### Accessors

`date-year`, `date-month`, `date-day`, `date-hour`, `date-minute`,
`date-second`, `date-millisecond`, `date-day-of-year`;
`(date-day-of-week t)` gives a lowercase symbol (`monday` … `sunday`);
`(date-only t)` truncates to midnight, kind preserved.

### Ordering

`date<?`, `date<=?`, `date>?`, `date>=?`, `date=?`, and the same five for
durations.

### Calendar arithmetic

Months and years have no fixed length, so these are calendar operations, not
durations — the day clamps when the target month is shorter:

| Form | Meaning |
|---|---|
| `(add-months t n)` / `(add-years t n)` | `(add-months (date 2024 1 31) 1)` is Feb 29. |
| `(leap-year? y)` / `(days-in-month y m)` | |

### Durations

Constructors `(days n)`, `(hours n)`, `(minutes n)`, `(seconds n)`,
`(milliseconds n)` accept exact or inexact numbers; combine them with `+` and
`-`. `(duration-negate d)` flips sign.

Component accessors wrap at their unit — `(duration-hours (hours 26))` is 2,
with `(duration-days …)` carrying the 1 — while totals do not:
`(duration-total-hours (hours 26))` is 26.0. Both families cover days, hours,
minutes, seconds, and milliseconds.

### Conversions

| Form | Meaning |
|---|---|
| `(date->local t)` / `(date->utc t)` | The only crossings into machine-local time. |
| `(date->unix t)` | Whole seconds since the epoch, floored, exact. |
| `(unix->date n)` | The inverse; negative values reach before 1970. |

### Formatting and parsing

Always the invariant culture.

| Form | Meaning |
|---|---|
| `(date->string t)` | ISO 8601 round-trip form (`"o"`). |
| `(date->string t fmt)` | A .NET format spec. |
| `(string->date s)` | Any ISO-ish form; a zoned string converts to UTC, an unzoned one is taken as already UTC — never as machine-local. `#f` on malformed input. |
| `(string->date s fmt)` | Exact parse against a spec; `#f` on mismatch. |
| `(duration->string d [fmt])` / `(string->duration s)` | `"1.02:30:00"` both ways; `#f` on malformed input. |

## Notes

- Nothing here performs host I/O beyond reading the clock and, in the two
  local-time conversions, the machine's time zone.
- `date=?` compares instants; two `DateTime`s with different kinds but equal
  ticks compare equal, as the CLR defines.
