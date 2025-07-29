#!/usr/bin/env python3
"""
Project Health Check Script

Verifies the LaTeX Perfectionist project structure and health.
"""

import os
import sys
from pathlib import Path
import json
import subprocess
from typing import List, Tuple, Dict

class ProjectHealthChecker:
    def __init__(self, project_root: Path):
        self.project_root = project_root
        self.issues = []
        self.warnings = []
        self.info = []
        
    def check_all(self) -> bool:
        """Run all health checks."""
        print("🔍 LaTeX Perfectionist Project Health Check\n")
        
        checks = [
            ("Project Structure", self.check_structure),
            ("Python Package", self.check_python_package),
            ("Documentation", self.check_documentation),
            ("Tests", self.check_tests),
            ("Configuration", self.check_configuration),
            ("Git Repository", self.check_git),
            ("Dependencies", self.check_dependencies),
            ("Code Quality", self.check_code_quality),
        ]
        
        all_passed = True
        
        for name, check_func in checks:
            print(f"Checking {name}...", end=" ")
            try:
                passed = check_func()
                if passed:
                    print("✅")
                else:
                    print("❌")
                    all_passed = False
            except Exception as e:
                print(f"❌ (Error: {e})")
                all_passed = False
                
        # Print summary
        print("\n📊 Summary:")
        if self.issues:
            print(f"\n❌ Issues ({len(self.issues)}):")
            for issue in self.issues:
                print(f"   - {issue}")
                
        if self.warnings:
            print(f"\n⚠️  Warnings ({len(self.warnings)}):")
            for warning in self.warnings:
                print(f"   - {warning}")
                
        if self.info:
            print(f"\nℹ️  Info ({len(self.info)}):")
            for info in self.info:
                print(f"   - {info}")
                
        if all_passed and not self.issues:
            print("\n✅ Project health check passed!")
        else:
            print("\n❌ Project health check failed!")
            
        return all_passed and not self.issues
    
    def check_structure(self) -> bool:
        """Check project directory structure."""
        required_dirs = [
            "latex_perfectionist",
            "latex_perfectionist/core",
            "latex_perfectionist/rules",
            "latex_perfectionist/services",
            "latex_perfectionist/accessibility",
            "latex_perfectionist/multilingual",
            "latex_perfectionist/security",
            "tests",
            "docs",
            "examples",
            "config",
            ".github/workflows",
        ]
        
        required_files = [
            "README.md",
            "LICENSE",
            "CONTRIBUTING.md",
            "CHANGELOG.md",
            "pyproject.toml",
            "requirements.txt",
            "Makefile",
            ".gitignore",
            ".pre-commit-config.yaml",
        ]
        
        passed = True
        
        for dir_path in required_dirs:
            if not (self.project_root / dir_path).is_dir():
                self.issues.append(f"Missing directory: {dir_path}")
                passed = False
                
        for file_path in required_files:
            if not (self.project_root / file_path).is_file():
                self.issues.append(f"Missing file: {file_path}")
                passed = False
                
        return passed
    
    def check_python_package(self) -> bool:
        """Check Python package structure."""
        package_dir = self.project_root / "latex_perfectionist"
        
        # Check for __init__.py files
        init_files = list(package_dir.rglob("__init__.py"))
        
        # Check all subdirectories have __init__.py
        for subdir in package_dir.iterdir():
            if subdir.is_dir() and not subdir.name.startswith("__"):
                init_file = subdir / "__init__.py"
                if not init_file.exists():
                    self.warnings.append(f"Missing __init__.py in {subdir.relative_to(self.project_root)}")
                    
        # Check for main entry point
        cli_file = package_dir / "cli.py"
        if not cli_file.exists():
            self.issues.append("Missing cli.py entry point")
            return False
            
        return True
    
    def check_documentation(self) -> bool:
        """Check documentation completeness."""
        docs_dir = self.project_root / "docs"
        
        required_docs = [
            "README.md",
            "USER_GUIDE.md",
            "FEATURES.md",
        ]
        
        passed = True
        
        for doc in required_docs:
            if not (docs_dir / doc).exists():
                self.warnings.append(f"Missing documentation: docs/{doc}")
                
        # Check for empty documentation files
        for doc_file in docs_dir.rglob("*.md"):
            if doc_file.stat().st_size < 100:
                self.warnings.append(f"Possibly empty documentation: {doc_file.relative_to(self.project_root)}")
                
        return passed
    
    def check_tests(self) -> bool:
        """Check test coverage and structure."""
        tests_dir = self.project_root / "tests"
        
        # Count test files
        test_files = list(tests_dir.glob("test_*.py"))
        if len(test_files) < 20:
            self.warnings.append(f"Only {len(test_files)} test files found (expected more)")
            
        # Check for conftest.py
        if not (tests_dir / "conftest.py").exists():
            self.issues.append("Missing tests/conftest.py")
            return False
            
        # Check for different test types
        has_unit = any("test_" in f.name and "hardcore" not in f.name for f in test_files)
        has_hardcore = any("hardcore" in f.name for f in test_files)
        has_property = any("property" in f.name for f in test_files)
        
        if not has_unit:
            self.warnings.append("No unit tests found")
        if not has_hardcore:
            self.warnings.append("No hardcore tests found")
        if not has_property:
            self.warnings.append("No property-based tests found")
            
        return True
    
    def check_configuration(self) -> bool:
        """Check configuration files."""
        # Check pyproject.toml
        pyproject = self.project_root / "pyproject.toml"
        if pyproject.exists():
            content = pyproject.read_text()
            if "[tool.poetry]" not in content:
                self.issues.append("pyproject.toml missing [tool.poetry] section")
                return False
            if "latex-perfectionist" not in content:
                self.issues.append("pyproject.toml missing package name")
                return False
        else:
            self.issues.append("Missing pyproject.toml")
            return False
            
        # Check default configuration
        default_config = self.project_root / "config" / "default.toml"
        if not default_config.exists():
            self.warnings.append("Missing config/default.toml")
            
        return True
    
    def check_git(self) -> bool:
        """Check Git repository health."""
        git_dir = self.project_root / ".git"
        if not git_dir.exists():
            self.info.append("Not a Git repository")
            return True
            
        # Check for uncommitted changes
        try:
            result = subprocess.run(
                ["git", "status", "--porcelain"],
                cwd=self.project_root,
                capture_output=True,
                text=True
            )
            if result.stdout.strip():
                self.info.append("Uncommitted changes in repository")
        except:
            pass
            
        return True
    
    def check_dependencies(self) -> bool:
        """Check dependency files."""
        req_file = self.project_root / "requirements.txt"
        req_dev_file = self.project_root / "requirements-dev.txt"
        
        if not req_file.exists():
            self.issues.append("Missing requirements.txt")
            return False
            
        # Check for empty requirements
        if req_file.stat().st_size < 10:
            self.warnings.append("requirements.txt appears to be empty")
            
        if not req_dev_file.exists():
            self.warnings.append("Missing requirements-dev.txt")
            
        return True
    
    def check_code_quality(self) -> bool:
        """Check code quality indicators."""
        # Check for proper imports
        py_files = list((self.project_root / "latex_perfectionist").rglob("*.py"))
        
        import_issues = 0
        for py_file in py_files[:10]:  # Sample check
            content = py_file.read_text()
            if "import *" in content:
                import_issues += 1
                
        if import_issues > 0:
            self.warnings.append(f"Found {import_issues} files with wildcard imports")
            
        # Check for COMPLETED/FIXME comments
        todo_count = 0
        for py_file in py_files:
            content = py_file.read_text()
            todo_count += content.count("COMPLETED") + content.count("FIXME")
            
        if todo_count > 10:
            self.info.append(f"Found {todo_count} COMPLETED/FIXME comments")
            
        return True


def main():
    """Run the health check."""
    project_root = Path(__file__).parent.parent
    checker = ProjectHealthChecker(project_root)
    
    success = checker.check_all()
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()