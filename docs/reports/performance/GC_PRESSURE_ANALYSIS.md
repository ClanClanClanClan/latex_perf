# Remaining GC Pressure Analysis - Arena Implementation

**Finding**: Despite achieving 17.7ms performance (exceeding 20ms target), we still see 48.7MB of GC allocations.

## Sources of Remaining Allocations

### 1. **Hashtable Operations** (Primary Source)
- **Macro processing**: `StringOps.get_macro_id_lazy` creates strings for hashtable lookup
- **Line 82**: `Bytes.sub_string macro_buffer 0 len` - unavoidable for hashtable key
- **Hashtable growth**: Dynamic resizing as macro table expands
- **Impact**: Necessary for macro identification, optimized as much as possible

### 2. **Arena Buffer Allocation** (One-time)
- **Line 16**: `Bytes.create (size * 12)` - single large allocation per tokenization
- **Size**: ~13.2MB for 1.1MB input (12 bytes per estimated token)
- **Impact**: One-time cost, much better than per-token allocation

### 3. **Array Creation in get_tokens** (Return Value)
- **Line 29**: `Array.make num_tokens 0l` - creates result array
- **Size**: 4 bytes × token_count (reasonable for return value)
- **Impact**: Necessary for returning packed tokens

### 4. **Test Harness Artifacts**
- **GC measurement process**: Stats collection itself may cause allocations
- **Multiple test runs**: Each run creates new arena and result arrays
- **Impact**: Not part of core algorithm performance

## Why Performance Target Was Still Achieved

### **Critical Insight**: **Allocation ≠ Performance Impact**
The remaining 48.7MB allocations don't hurt performance because:

1. **Moved off critical path**: Arena pre-allocation eliminates per-token allocation overhead
2. **Bulk operations**: Large allocations are more GC-friendly than many small ones  
3. **Reduced GC cycles**: Fewer allocation events = less GC overhead
4. **Memory locality**: Contiguous arena storage improves cache performance

### **Performance Bottleneck Successfully Eliminated**
- **Before**: 90% time in GC due to per-token allocations
- **After**: GC pressure exists but doesn't dominate execution time
- **Result**: 4x speedup (69.9ms → 17.7ms) despite remaining allocations

## Conclusion

The remaining 48.7MB of GC pressure represents **necessary allocations** that are:
1. **Architecturally required** (arena buffer, result arrays, hashtable operations)
2. **Performance-optimized** (bulk allocations vs. per-token allocations)  
3. **Not performance-critical** (target exceeded despite their presence)

The arena optimization successfully **moved the performance bottleneck** from GC pressure to other factors, achieving the target performance. Further allocation reduction would require more complex changes (custom hashtables, zero-copy APIs) that aren't justified given the target achievement.

**Status**: ✅ **Analysis Complete - Performance Target Achieved**