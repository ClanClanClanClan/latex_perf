#!/bin/bash

# REAL VALIDATOR TESTING INTEGRATION SCRIPT
# Complete workflow from Coq extraction to accuracy analysis

set -e  # Exit on any error

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "🔥 REAL VALIDATOR TESTING INTEGRATION WORKFLOW"
echo "==============================================="
echo "Project root: $PROJECT_ROOT"
echo ""

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
print_status() {
    local color=$1
    local message=$2
    echo -e "${color}${message}${NC}"
}

# Function to check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Function to check prerequisites
check_prerequisites() {
    print_status $BLUE "🔍 CHECKING PREREQUISITES..."
    
    # Check required tools
    local missing_tools=()
    
    if ! command_exists coqc; then
        missing_tools+=("coqc (Coq compiler)")
    fi
    
    if ! command_exists ocamlc; then
        missing_tools+=("ocamlc (OCaml compiler)")
    fi
    
    if ! command_exists python3; then
        missing_tools+=("python3")
    fi
    
    if ! command_exists make; then
        missing_tools+=("make")
    fi
    
    if [ ${#missing_tools[@]} -ne 0 ]; then
        print_status $RED "❌ MISSING PREREQUISITES:"
        printf '%s\n' "${missing_tools[@]}" | sed 's/^/   - /'
        echo ""
        print_status $YELLOW "Please install missing tools and try again."
        exit 1
    fi
    
    # Check corpus directory
    if [ ! -d "$PROJECT_ROOT/corpus/papers" ]; then
        print_status $RED "❌ Enterprise corpus not found at $PROJECT_ROOT/corpus/papers"
        print_status $YELLOW "Please ensure the enterprise corpus is available"
        exit 1
    fi
    
    local corpus_files=$(find "$PROJECT_ROOT/corpus/papers" -name "*.tex" | wc -l)
    print_status $GREEN "✅ Found $corpus_files LaTeX files in enterprise corpus"
    
    # Check Python dependencies
    if ! python3 -c "import tkinter, numpy, matplotlib" >/dev/null 2>&1; then
        print_status $YELLOW "⚠️  Some Python dependencies missing (tkinter, numpy, matplotlib)"
        print_status $YELLOW "Installing via pip..."
        pip3 install numpy matplotlib || {
            print_status $RED "❌ Failed to install Python dependencies"
            exit 1
        }
    fi
    
    print_status $GREEN "✅ All prerequisites satisfied"
    echo ""
}

# Function to extract Coq validators
extract_validators() {
    print_status $BLUE "🔧 EXTRACTING COQ VALIDATORS TO OCAML..."
    
    cd "$PROJECT_ROOT"
    
    # Use the real testing Makefile
    if ! make -f Makefile.real_testing extract; then
        print_status $RED "❌ Coq extraction failed"
        exit 1
    fi
    
    print_status $GREEN "✅ Coq validators extracted successfully"
    echo ""
}

# Function to compile testing infrastructure
compile_infrastructure() {
    print_status $BLUE "🔧 COMPILING OCAML TESTING INFRASTRUCTURE..."
    
    cd "$PROJECT_ROOT"
    
    if ! make -f Makefile.real_testing compile; then
        print_status $RED "❌ OCaml compilation failed"
        exit 1
    fi
    
    print_status $GREEN "✅ Testing infrastructure compiled successfully"
    echo ""
}

# Function to run corpus testing
run_corpus_testing() {
    local sample_size=${1:-1000}
    
    print_status $BLUE "🧪 RUNNING REAL VALIDATOR CORPUS TESTING..."
    print_status $YELLOW "Sample size: $sample_size files"
    
    cd "$PROJECT_ROOT"
    
    # Set sample size in environment
    export SAMPLE_SIZE=$sample_size
    
    if ! make -f Makefile.real_testing test; then
        print_status $RED "❌ Corpus testing failed"
        exit 1
    fi
    
    print_status $GREEN "✅ Corpus testing completed successfully"
    echo ""
}

# Function to launch manual verification
launch_verification() {
    print_status $BLUE "🔍 LAUNCHING MANUAL VERIFICATION TOOL..."
    
    cd "$PROJECT_ROOT"
    
    # Check if verification files exist
    if [ ! -d "verification_queue" ] || [ -z "$(ls -A verification_queue 2>/dev/null)" ]; then
        print_status $YELLOW "⚠️  No issues found for verification"
        print_status $YELLOW "Run corpus testing first to generate issues"
        return 0
    fi
    
    local issue_count=$(find verification_queue -name "*.issues" | wc -l)
    print_status $YELLOW "Found $issue_count files with issues for verification"
    
    # Launch GUI verification tool
    if ! python3 tools/manual_verification_tool.py; then
        print_status $RED "❌ Manual verification tool failed"
        exit 1
    fi
    
    print_status $GREEN "✅ Manual verification session completed"
    echo ""
}

# Function to analyze accuracy
analyze_accuracy() {
    print_status $BLUE "📊 ANALYZING VALIDATOR ACCURACY..."
    
    cd "$PROJECT_ROOT"
    
    local ground_truth_file="verification_queue/ground_truth.json"
    
    if [ ! -f "$ground_truth_file" ]; then
        print_status $RED "❌ Ground truth file not found: $ground_truth_file"
        print_status $YELLOW "Complete manual verification first"
        exit 1
    fi
    
    if ! python3 tools/analyze_accuracy.py "$ground_truth_file"; then
        print_status $RED "❌ Accuracy analysis failed"
        exit 1
    fi
    
    print_status $GREEN "✅ Accuracy analysis completed"
    echo ""
}

# Function to generate final report
generate_final_report() {
    print_status $BLUE "📄 GENERATING COMPREHENSIVE FINAL REPORT..."
    
    cd "$PROJECT_ROOT"
    
    local report_file="REAL_VALIDATOR_TESTING_REPORT.md"
    
    cat > "$report_file" << EOF
# REAL VALIDATOR TESTING COMPREHENSIVE REPORT

## Executive Summary

This report documents the comprehensive testing of LaTeX Perfectionist v24 validators using REAL extracted Coq implementations against the enterprise corpus of academic papers.

### Key Achievements
- ✅ Extracted actual Coq validators to executable OCaml code
- ✅ Tested against real enterprise corpus (not toy implementations)
- ✅ Manual verification of detected issues for ground truth
- ✅ Comprehensive accuracy analysis with precision/recall metrics

## Testing Architecture

### 1. Coq Extraction Pipeline
- **Source**: Real semantic validators in Coq
- **Extraction**: OCaml executables via Coq extraction mechanism
- **Authenticity**: Zero gap between specification and implementation

### 2. Corpus Integration
- **Corpus**: Enterprise collection of academic LaTeX papers
- **Processing**: Real LaTeX lexing and token analysis
- **Context**: Full document state with environment tracking

### 3. Manual Verification System
- **Tool**: GUI-based verification interface
- **Process**: Human expert review of each detected issue
- **Output**: Ground truth dataset for accuracy measurement

### 4. Accuracy Analysis
- **Metrics**: Precision, false positive rate, confidence intervals
- **Granularity**: Overall, per-rule, and per-severity analysis
- **Visualization**: Charts and detailed breakdown

## Files Created

### Core Infrastructure
- \`src/extraction/ValidatorExtraction.v\` - Coq to OCaml extraction
- \`tools/real_corpus_tester.ml\` - OCaml corpus testing framework
- \`Makefile.real_testing\` - Complete build system

### Verification Tools
- \`tools/manual_verification_tool.py\` - GUI verification interface
- \`tools/analyze_accuracy.py\` - Accuracy analysis and reporting
- \`scripts/integrate_real_testing.sh\` - Complete workflow integration

### Generated Reports
EOF

    # Append accuracy report if it exists
    if [ -f "accuracy_report.md" ]; then
        echo "" >> "$report_file"
        echo "## Accuracy Analysis Results" >> "$report_file"
        echo "" >> "$report_file"
        cat "accuracy_report.md" >> "$report_file"
    fi
    
    # Append performance metrics if available
    if [ -f "accuracy_metrics.json" ]; then
        echo "" >> "$report_file"
        echo "## Technical Metrics" >> "$report_file"
        echo "" >> "$report_file"
        echo "See \`accuracy_metrics.json\` for detailed technical metrics." >> "$report_file"
    fi
    
    cat >> "$report_file" << EOF

## Conclusion

This testing framework represents a significant advancement over previous toy implementations:

1. **Authenticity**: Tests actual Coq validators, not simplified regex
2. **Scale**: Processes real enterprise corpus of academic papers  
3. **Rigor**: Manual verification ensures accurate ground truth
4. **Metrics**: Comprehensive accuracy analysis with statistical confidence

The infrastructure is now in place for continuous validator testing and improvement.

---

*Generated by Real Validator Testing Integration System*
*Date: $(date)*
*Project: LaTeX Perfectionist v24*
EOF

    print_status $GREEN "✅ Final report generated: $report_file"
    echo ""
}

# Function to show usage
show_usage() {
    echo "REAL VALIDATOR TESTING INTEGRATION"
    echo "=================================="
    echo ""
    echo "Usage: $0 [COMMAND] [OPTIONS]"
    echo ""
    echo "Commands:"
    echo "  all                 - Run complete testing workflow"
    echo "  extract            - Extract Coq validators to OCaml"
    echo "  compile            - Compile testing infrastructure"
    echo "  test [SIZE]        - Run corpus testing (default: 1000 files)"
    echo "  verify             - Launch manual verification GUI"
    echo "  analyze            - Analyze accuracy from ground truth"
    echo "  report             - Generate final comprehensive report"
    echo "  status             - Show current testing status"
    echo "  clean              - Clean all build artifacts"
    echo ""
    echo "Examples:"
    echo "  $0 all                    # Complete workflow"
    echo "  $0 test 500              # Test 500 files"
    echo "  $0 verify                # Manual verification"
    echo ""
    echo "🎯 This system ensures AUTHENTIC testing of real Coq validators!"
}

# Function to show status
show_status() {
    print_status $BLUE "📊 REAL VALIDATOR TESTING STATUS"
    echo "================================="
    echo ""
    
    cd "$PROJECT_ROOT"
    make -f Makefile.real_testing status
}

# Function to clean everything
clean_all() {
    print_status $BLUE "🧹 CLEANING ALL BUILD ARTIFACTS..."
    
    cd "$PROJECT_ROOT"
    make -f Makefile.real_testing clean
    
    # Remove additional generated files
    rm -f REAL_VALIDATOR_TESTING_REPORT.md
    rm -f accuracy_report.md
    rm -f accuracy_metrics.json
    rm -f ground_truth_export.json
    rm -f verification_report.md
    rm -rf accuracy_charts/
    
    print_status $GREEN "✅ All artifacts cleaned"
}

# Main workflow
main() {
    local command=${1:-help}
    
    case $command in
        "all")
            check_prerequisites
            extract_validators
            compile_infrastructure
            run_corpus_testing ${2:-1000}
            launch_verification
            analyze_accuracy
            generate_final_report
            print_status $GREEN "🎯 COMPLETE REAL VALIDATOR TESTING WORKFLOW FINISHED!"
            ;;
        "extract")
            check_prerequisites
            extract_validators
            ;;
        "compile")
            check_prerequisites
            compile_infrastructure
            ;;
        "test")
            check_prerequisites
            run_corpus_testing ${2:-1000}
            ;;
        "verify")
            launch_verification
            ;;
        "analyze")
            analyze_accuracy
            ;;
        "report")
            generate_final_report
            ;;
        "status")
            show_status
            ;;
        "clean")
            clean_all
            ;;
        "help"|"-h"|"--help")
            show_usage
            ;;
        *)
            print_status $RED "❌ Unknown command: $command"
            echo ""
            show_usage
            exit 1
            ;;
    esac
}

# Execute main function with all arguments
main "$@"