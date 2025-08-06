# 🚨 CRYSTAL CLEAR TOKEN ADT STATUS 🚨

**FOR ALL FUTURE SESSIONS - READ THIS FIRST**

## The Situation

1. **The Problem:** Documentation says "9 constructors", implementation has 6 constructors
2. **The Decision:** Keep 6 constructors as canonical (decided 2025-07-31)
3. **The Status:** Documentation updates IN PROGRESS

## What IS Correct (The Truth)

```ocaml
(* THIS IS THE CORRECT TOKEN TYPE - 6 CONSTRUCTORS *)
type token =
  | TChar       of Uchar.t * Catcode.t    (* UTF-8 character *)
  | TMacro      of string                 (* \command *)
  | TParam      of int                    (* #1 through #9 *)
  | TGroupOpen                            (* { *)
  | TGroupClose                           (* } *)
  | TEOF                                  (* end marker *)
```

**COUNT THEM: 6 constructors, NOT 9!**

## What Needs Fixing

### ❌ WRONG (Old Documentation)
- "Nine-constructor type token"
- "9 constructors total"
- Fixed size "24 B on 64-bit"
- Record type definition with {cat; text; loc}

### ✅ CORRECT (New Documentation)
- "Six-constructor sum type"
- "6 constructors"
- Variable sizes per variant (see table)
- Sum type with variants as shown above

## Files That Need Updates

1. **Appendices v25.md** - Line 104 says "Nine-constructor" → Change to "Six-constructor"
2. **Appendices v25.md** - Section B-1-2 shows wrong type definition → Replace with sum type
3. **v25_master.md** - Check for any "9 constructor" references
4. **v25_master.yaml** - Check for any "9 constructor" references
5. **PLANNER.yaml** - Known to have "9 constructors total" comment

## What Has Been Done

✅ Created decision log: `/docs/decisions/2025-07-31-token-adt.md`
✅ Created update guide: `/docs/TOKEN_ADT_UPDATE_GUIDE.md`
✅ Created CI script: `/scripts/size_check.ml`
✅ Updated line 104 in Appendices v25.md (Nine → Six)
❌ Still need to update the type definition in B-1-2
❌ Still need to check other files

## Memory Sizes (The Real Numbers)

| Variant    | x86-64 | arm64 | 
|------------|--------|-------|
| TChar      | 24 B   | 24 B  |
| TMacro     | 24 B   | 24 B  |
| TParam     | 16 B   | 16 B  |
| TGroupOpen | 8 B    | 8 B   |
| TGroupClose| 8 B    | 8 B   |
| TEOF       | 8 B    | 8 B   |
| Average    | 17.3 B | 17.3 B|

## CI Guards (Prevent Future Confusion)

1. **Token constructor count check** - Fails if count ≠ 6
2. **Size drift check** - Fails if sizes change > 8 bytes
3. **Documentation grep** - Fails if "Nine-constructor" found

## For Next Session

If you're continuing this work:
1. Read `/docs/decisions/2025-07-31-token-adt.md`
2. Follow `/docs/TOKEN_ADT_UPDATE_GUIDE.md`
3. The manual edits to Appendices v25.md Section B-1-2 are tricky due to special characters
4. Remember: 6 CONSTRUCTORS, NOT 9!

**Target Completion:** 2025-08-02 18:00 UTC (end of Week 6)

---
*This is the single source of truth for the token ADT situation.*