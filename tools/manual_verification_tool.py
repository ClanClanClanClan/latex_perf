#!/usr/bin/env python3
"""
MANUAL VERIFICATION TOOL - Ground Truth Creation
Helps manually verify validator results to build ground truth dataset.
"""

import os
import json
import sys
from pathlib import Path
from typing import Dict, List, Any
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext

class ValidationIssue:
    def __init__(self, rule_id: str, severity: str, message: str, line: int):
        self.rule_id = rule_id
        self.severity = severity
        self.message = message
        self.line = line
        self.verified = False
        self.is_true_positive = None
        self.notes = ""

class ManualVerifier:
    def __init__(self):
        self.verification_dir = Path("verification_queue")
        self.corpus_dir = Path("corpus/papers")
        self.ground_truth_file = Path("verification_queue/ground_truth.json")
        self.ground_truth = self.load_ground_truth()
        
        # GUI setup
        self.root = tk.Tk()
        self.root.title("LaTeX Validator Manual Verification Tool")
        self.root.geometry("1200x800")
        
        self.current_file = None
        self.current_issues = []
        self.current_issue_index = 0
        
        self.setup_gui()
        self.load_file_list()
    
    def load_ground_truth(self) -> Dict[str, Any]:
        """Load existing ground truth data"""
        if self.ground_truth_file.exists():
            with open(self.ground_truth_file, 'r') as f:
                return json.load(f)
        return {
            "verified_files": {},
            "statistics": {
                "total_issues": 0,
                "true_positives": 0,
                "false_positives": 0,
                "files_verified": 0
            },
            "rule_accuracy": {}
        }
    
    def save_ground_truth(self):
        """Save ground truth data to file"""
        with open(self.ground_truth_file, 'w') as f:
            json.dump(self.ground_truth, f, indent=2)
    
    def setup_gui(self):
        """Setup the GUI interface"""
        # Main frame
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # File selection frame
        file_frame = ttk.LabelFrame(main_frame, text="Files to Verify")
        file_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.file_listbox = tk.Listbox(file_frame, height=6)
        self.file_listbox.pack(fill=tk.X, padx=5, pady=5)
        self.file_listbox.bind('<<ListboxSelect>>', self.on_file_select)
        
        # File info frame
        info_frame = ttk.LabelFrame(main_frame, text="File Information")
        info_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.file_info_label = ttk.Label(info_frame, text="No file selected")
        self.file_info_label.pack(padx=5, pady=5)
        
        # Issue verification frame
        issue_frame = ttk.LabelFrame(main_frame, text="Issue Verification")
        issue_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        
        # Issue navigation
        nav_frame = ttk.Frame(issue_frame)
        nav_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(nav_frame, text="Previous", command=self.prev_issue).pack(side=tk.LEFT)
        self.issue_counter_label = ttk.Label(nav_frame, text="Issue 0/0")
        self.issue_counter_label.pack(side=tk.LEFT, padx=10)
        ttk.Button(nav_frame, text="Next", command=self.next_issue).pack(side=tk.LEFT)
        
        # Issue details
        details_frame = ttk.Frame(issue_frame)
        details_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(details_frame, text="Rule ID:").grid(row=0, column=0, sticky=tk.W)
        self.rule_id_label = ttk.Label(details_frame, text="")
        self.rule_id_label.grid(row=0, column=1, sticky=tk.W, padx=10)
        
        ttk.Label(details_frame, text="Severity:").grid(row=1, column=0, sticky=tk.W)
        self.severity_label = ttk.Label(details_frame, text="")
        self.severity_label.grid(row=1, column=1, sticky=tk.W, padx=10)
        
        ttk.Label(details_frame, text="Message:").grid(row=2, column=0, sticky=tk.W)
        self.message_label = ttk.Label(details_frame, text="", wraplength=400)
        self.message_label.grid(row=2, column=1, sticky=tk.W, padx=10)
        
        ttk.Label(details_frame, text="Line:").grid(row=3, column=0, sticky=tk.W)
        self.line_label = ttk.Label(details_frame, text="")
        self.line_label.grid(row=3, column=1, sticky=tk.W, padx=10)
        
        # LaTeX content display
        content_frame = ttk.LabelFrame(issue_frame, text="LaTeX Content (around line)")
        content_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        self.content_text = scrolledtext.ScrolledText(content_frame, height=10, state=tk.DISABLED)
        self.content_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Verification controls
        verify_frame = ttk.Frame(issue_frame)
        verify_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(verify_frame, text="Verification:").pack(side=tk.LEFT)
        
        self.verification_var = tk.StringVar(value="unverified")
        ttk.Radiobutton(verify_frame, text="True Positive", variable=self.verification_var, 
                       value="true_positive", command=self.on_verification_change).pack(side=tk.LEFT, padx=10)
        ttk.Radiobutton(verify_frame, text="False Positive", variable=self.verification_var,
                       value="false_positive", command=self.on_verification_change).pack(side=tk.LEFT, padx=10)
        
        # Notes
        notes_frame = ttk.LabelFrame(issue_frame, text="Verification Notes")
        notes_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.notes_text = tk.Text(notes_frame, height=3)
        self.notes_text.pack(fill=tk.X, padx=5, pady=5)
        self.notes_text.bind('<KeyRelease>', self.on_notes_change)
        
        # Control buttons
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(fill=tk.X, pady=10)
        
        ttk.Button(button_frame, text="Save Progress", command=self.save_progress).pack(side=tk.LEFT)
        ttk.Button(button_frame, text="Generate Report", command=self.generate_report).pack(side=tk.LEFT, padx=10)
        ttk.Button(button_frame, text="Export Ground Truth", command=self.export_ground_truth).pack(side=tk.LEFT, padx=10)
        
        # Statistics display
        stats_frame = ttk.LabelFrame(main_frame, text="Verification Statistics")
        stats_frame.pack(fill=tk.X, pady=(10, 0))
        
        self.stats_label = ttk.Label(stats_frame, text="No statistics available")
        self.stats_label.pack(padx=5, pady=5)
        
        self.update_statistics_display()
    
    def load_file_list(self):
        """Load list of files with issues to verify"""
        if not self.verification_dir.exists():
            messagebox.showerror("Error", f"Verification directory {self.verification_dir} not found")
            return
        
        issue_files = list(self.verification_dir.glob("*.issues"))
        self.file_listbox.delete(0, tk.END)
        
        for issue_file in sorted(issue_files):
            filename = issue_file.stem  # Remove .issues extension
            verification_status = "✅" if filename in self.ground_truth["verified_files"] else "❌"
            self.file_listbox.insert(tk.END, f"{verification_status} {filename}")
    
    def on_file_select(self, event):
        """Handle file selection"""
        selection = self.file_listbox.curselection()
        if not selection:
            return
        
        selected_text = self.file_listbox.get(selection[0])
        filename = selected_text[2:]  # Remove status emoji
        
        self.load_file_issues(filename)
    
    def load_file_issues(self, filename: str):
        """Load issues for a specific file"""
        self.current_file = filename
        issue_file = self.verification_dir / f"{filename}.issues"
        
        if not issue_file.exists():
            messagebox.showerror("Error", f"Issue file {issue_file} not found")
            return
        
        # Parse issue file
        self.current_issues = []
        with open(issue_file, 'r') as f:
            for line in f:
                if line.strip().startswith("RULE:"):
                    parts = line.strip().split(" | ")
                    if len(parts) >= 4:
                        rule_id = parts[0].split(": ")[1]
                        severity = parts[1].split(": ")[1] 
                        message = parts[2].split(": ")[1]
                        line_num = int(parts[3].split(": ")[1])
                        
                        issue = ValidationIssue(rule_id, severity, message, line_num)
                        
                        # Load existing verification data
                        if filename in self.ground_truth["verified_files"]:
                            file_data = self.ground_truth["verified_files"][filename]
                            issue_key = f"{rule_id}_{line_num}"
                            if issue_key in file_data:
                                issue.verified = True
                                issue.is_true_positive = file_data[issue_key]["is_true_positive"] 
                                issue.notes = file_data[issue_key].get("notes", "")
                        
                        self.current_issues.append(issue)
        
        self.current_issue_index = 0
        self.update_file_info()
        self.display_current_issue()
    
    def update_file_info(self):
        """Update file information display"""
        if self.current_file:
            total_issues = len(self.current_issues)
            verified_issues = sum(1 for issue in self.current_issues if issue.verified)
            self.file_info_label.config(text=f"File: {self.current_file} | Issues: {total_issues} | Verified: {verified_issues}")
        else:
            self.file_info_label.config(text="No file selected")
    
    def display_current_issue(self):
        """Display the current issue for verification"""
        if not self.current_issues:
            return
        
        issue = self.current_issues[self.current_issue_index]
        
        # Update issue counter
        self.issue_counter_label.config(text=f"Issue {self.current_issue_index + 1}/{len(self.current_issues)}")
        
        # Update issue details
        self.rule_id_label.config(text=issue.rule_id)
        self.severity_label.config(text=issue.severity)
        self.message_label.config(text=issue.message)
        self.line_label.config(text=str(issue.line))
        
        # Update verification status
        if issue.verified:
            if issue.is_true_positive:
                self.verification_var.set("true_positive")
            else:
                self.verification_var.set("false_positive")
        else:
            self.verification_var.set("unverified")
        
        # Update notes
        self.notes_text.delete(1.0, tk.END)
        self.notes_text.insert(1.0, issue.notes)
        
        # Load and display LaTeX content
        self.display_latex_content(issue.line)
    
    def display_latex_content(self, target_line: int):
        """Display LaTeX content around the target line"""
        latex_file = self.find_latex_file(self.current_file)
        if not latex_file or not latex_file.exists():
            self.content_text.config(state=tk.NORMAL)
            self.content_text.delete(1.0, tk.END)
            self.content_text.insert(1.0, f"LaTeX file not found: {latex_file}")
            self.content_text.config(state=tk.DISABLED)
            return
        
        try:
            with open(latex_file, 'r', encoding='utf-8', errors='ignore') as f:
                lines = f.readlines()
            
            # Show context around target line
            start_line = max(0, target_line - 10)
            end_line = min(len(lines), target_line + 10)
            
            self.content_text.config(state=tk.NORMAL)
            self.content_text.delete(1.0, tk.END)
            
            for i in range(start_line, end_line):
                line_num = i + 1
                line_content = lines[i].rstrip()
                
                if line_num == target_line:
                    # Highlight the target line
                    self.content_text.insert(tk.END, f">>> {line_num:3d}: {line_content}\n")
                else:
                    self.content_text.insert(tk.END, f"    {line_num:3d}: {line_content}\n")
            
            self.content_text.config(state=tk.DISABLED)
            
        except Exception as e:
            self.content_text.config(state=tk.NORMAL)
            self.content_text.delete(1.0, tk.END)
            self.content_text.insert(1.0, f"Error reading LaTeX file: {str(e)}")
            self.content_text.config(state=tk.DISABLED)
    
    def find_latex_file(self, filename: str) -> Path:
        """Find the corresponding LaTeX file in the corpus"""
        # Try different possible locations
        possible_paths = [
            self.corpus_dir / f"{filename}.tex",
            self.corpus_dir / filename,
        ]
        
        # Search recursively in corpus directory
        for tex_file in self.corpus_dir.rglob("*.tex"):
            if tex_file.stem == filename or tex_file.name == filename:
                return tex_file
        
        return None
    
    def prev_issue(self):
        """Navigate to previous issue"""
        if self.current_issues and self.current_issue_index > 0:
            self.save_current_issue()
            self.current_issue_index -= 1
            self.display_current_issue()
    
    def next_issue(self):
        """Navigate to next issue"""
        if self.current_issues and self.current_issue_index < len(self.current_issues) - 1:
            self.save_current_issue()
            self.current_issue_index += 1
            self.display_current_issue()
    
    def on_verification_change(self):
        """Handle verification status change"""
        if self.current_issues:
            issue = self.current_issues[self.current_issue_index]
            verification = self.verification_var.get()
            
            if verification != "unverified":
                issue.verified = True
                issue.is_true_positive = (verification == "true_positive")
            else:
                issue.verified = False
                issue.is_true_positive = None
    
    def on_notes_change(self, event=None):
        """Handle notes text change"""
        if self.current_issues:
            issue = self.current_issues[self.current_issue_index]
            issue.notes = self.notes_text.get(1.0, tk.END).strip()
    
    def save_current_issue(self):
        """Save verification data for current issue"""
        if not self.current_issues or not self.current_file:
            return
        
        issue = self.current_issues[self.current_issue_index]
        
        if self.current_file not in self.ground_truth["verified_files"]:
            self.ground_truth["verified_files"][self.current_file] = {}
        
        issue_key = f"{issue.rule_id}_{issue.line}"
        self.ground_truth["verified_files"][self.current_file][issue_key] = {
            "rule_id": issue.rule_id,
            "severity": issue.severity, 
            "message": issue.message,
            "line": issue.line,
            "verified": issue.verified,
            "is_true_positive": issue.is_true_positive,
            "notes": issue.notes
        }
    
    def save_progress(self):
        """Save all verification progress"""
        if self.current_issues:
            self.save_current_issue()
        
        self.update_ground_truth_statistics()
        self.save_ground_truth()
        self.update_statistics_display()
        self.load_file_list()  # Refresh file list with updated status
        
        messagebox.showinfo("Success", "Verification progress saved successfully!")
    
    def update_ground_truth_statistics(self):
        """Update statistics in ground truth data"""
        stats = {
            "total_issues": 0,
            "true_positives": 0,
            "false_positives": 0,
            "files_verified": len(self.ground_truth["verified_files"]),
            "unverified_issues": 0
        }
        
        rule_stats = {}
        
        for filename, file_data in self.ground_truth["verified_files"].items():
            for issue_key, issue_data in file_data.items():
                rule_id = issue_data["rule_id"]
                
                if rule_id not in rule_stats:
                    rule_stats[rule_id] = {"total": 0, "true_positives": 0, "false_positives": 0}
                
                rule_stats[rule_id]["total"] += 1
                stats["total_issues"] += 1
                
                if issue_data["verified"]:
                    if issue_data["is_true_positive"]:
                        stats["true_positives"] += 1
                        rule_stats[rule_id]["true_positives"] += 1
                    else:
                        stats["false_positives"] += 1
                        rule_stats[rule_id]["false_positives"] += 1
                else:
                    stats["unverified_issues"] += 1
        
        self.ground_truth["statistics"] = stats
        self.ground_truth["rule_accuracy"] = rule_stats
    
    def update_statistics_display(self):
        """Update the statistics display"""
        stats = self.ground_truth["statistics"]
        
        total = stats.get("total_issues", 0)
        true_pos = stats.get("true_positives", 0)
        false_pos = stats.get("false_positives", 0)
        unverified = stats.get("unverified_issues", 0)
        files_verified = stats.get("files_verified", 0)
        
        if total > 0:
            precision = (true_pos / (true_pos + false_pos)) * 100 if (true_pos + false_pos) > 0 else 0
            stats_text = (f"Files Verified: {files_verified} | "
                         f"Total Issues: {total} | "
                         f"True Positives: {true_pos} | "
                         f"False Positives: {false_pos} | "
                         f"Unverified: {unverified} | "
                         f"Precision: {precision:.1f}%")
        else:
            stats_text = "No verification data available"
        
        self.stats_label.config(text=stats_text)
    
    def generate_report(self):
        """Generate verification report"""
        report_file = Path("verification_report.md")
        
        with open(report_file, 'w') as f:
            f.write("# LaTeX Validator Manual Verification Report\n\n")
            
            stats = self.ground_truth["statistics"]
            f.write("## Overall Statistics\n\n")
            f.write(f"- Files Verified: {stats.get('files_verified', 0)}\n")
            f.write(f"- Total Issues: {stats.get('total_issues', 0)}\n")
            f.write(f"- True Positives: {stats.get('true_positives', 0)}\n")
            f.write(f"- False Positives: {stats.get('false_positives', 0)}\n")
            
            if stats.get('total_issues', 0) > 0:
                precision = (stats.get('true_positives', 0) / (stats.get('true_positives', 0) + stats.get('false_positives', 0))) * 100
                f.write(f"- Precision: {precision:.1f}%\n")
            
            f.write("\n## Rule-by-Rule Accuracy\n\n")
            for rule_id, rule_stats in self.ground_truth["rule_accuracy"].items():
                total = rule_stats["total"]
                true_pos = rule_stats["true_positives"]
                false_pos = rule_stats["false_positives"]
                
                if total > 0:
                    precision = (true_pos / (true_pos + false_pos)) * 100 if (true_pos + false_pos) > 0 else 0
                    f.write(f"- **{rule_id}**: {total} issues, {true_pos} TP, {false_pos} FP, {precision:.1f}% precision\n")
        
        messagebox.showinfo("Success", f"Verification report generated: {report_file}")
    
    def export_ground_truth(self):
        """Export ground truth for use in automated accuracy testing"""
        export_file = Path("ground_truth_export.json")
        
        export_data = {
            "metadata": {
                "export_date": str(Path(__file__).stat().st_mtime),
                "total_files": len(self.ground_truth["verified_files"]),
                "total_issues": self.ground_truth["statistics"].get("total_issues", 0)
            },
            "ground_truth": self.ground_truth["verified_files"],
            "statistics": self.ground_truth["statistics"],
            "rule_accuracy": self.ground_truth["rule_accuracy"]
        }
        
        with open(export_file, 'w') as f:
            json.dump(export_data, f, indent=2)
        
        messagebox.showinfo("Success", f"Ground truth exported: {export_file}")
    
    def run(self):
        """Run the manual verification tool"""
        self.root.mainloop()

def main():
    """Main function"""
    print("🔍 MANUAL VERIFICATION TOOL")
    print("===========================")
    print("Starting GUI for manual verification of validator results...")
    
    verifier = ManualVerifier()
    verifier.run()

if __name__ == "__main__":
    main()