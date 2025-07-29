#!/bin/bash
echo "=== Corpus Integrity Check ==="
echo "Timestamp: $(date)"
echo ""

# Check perfect corpus
if [[ -d "corpus/perfect_corpus" ]]; then
    paper_count=$(find corpus/perfect_corpus/papers -type d -mindepth 1 | wc -l)
    metadata_count=$(find corpus/perfect_corpus/metadata -name "*.json" | wc -l)
    ground_truth_count=$(find corpus/perfect_corpus/ground_truth -name "*.json" | wc -l)
    
    echo "Perfect Corpus Status:"
    echo "  Papers: $paper_count"
    echo "  Metadata: $metadata_count" 
    echo "  Ground Truth: $ground_truth_count"
    
    # Check validation reports
    validation_reports=$(find corpus/perfect_corpus -name "validation_report_*.md" | wc -l)
    echo "  Validation Reports: $validation_reports"
    
    # Check LaTeX epsilon spec
    if [[ -f "corpus/perfect_corpus/LATEX_EPSILON_SPECIFICATION.md" ]]; then
        echo "  LaTeX ε Specification: ✅ Found"
    else
        echo "  LaTeX ε Specification: ❌ Missing"
    fi
    
    if [[ $paper_count -lt 1000 ]]; then
        echo ""
        echo "WARNING: Paper count seems low! Expected 1000+"
        exit 1
    fi
else
    echo "ERROR: Perfect corpus missing!"
    exit 1
fi

echo ""

# Check main corpus
if [[ -d "corpus/papers" ]]; then
    main_paper_count=$(find corpus/papers -type d -mindepth 1 | wc -l)
    main_tex_count=$(find corpus/papers -name "*.tex" | wc -l)
    echo "Main Corpus Status:"
    echo "  Paper directories: $main_paper_count"
    echo "  TeX files: $main_tex_count"
else
    echo "Main corpus not found (may be expected)"
fi

echo ""

# Check corpus scripts
echo "Corpus Scripts:"
for script in perfect_corpus_builder.py validate_perfect_corpus.py; do
    if [[ -f "corpus/$script" ]]; then
        echo "  $script: ✅ Found"
    else
        echo "  $script: ❌ Missing"
    fi
done

echo ""
echo "=== Corpus Integrity: PASSED ==="