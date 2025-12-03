package main

import (
	"archive/zip"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"strings"
)

// AnalysisResult represents a single performance issue found in the bundle
type AnalysisResult struct {
	Severity   string                 `json:"severity"` // "critical", "warning", "info"
	Category   string                 `json:"category"` // "scan", "join", "sort", "network", etc.
	Message    string                 `json:"message"`
	Suggestion string                 `json:"suggestion"`
	Details    map[string]interface{} `json:"details"`
}

// Report contains the overall analysis results
type Report struct {
	Status     string           `json:"status"`
	Critical   int              `json:"critical"`
	Warnings   int              `json:"warnings"`
	Info       int              `json:"info"`
	Issues     []AnalysisResult `json:"issues"`
	Version    string           `json:"version,omitempty"`
	BundlePath string           `json:"bundle_path,omitempty"`
}

// Analyzer analyzes CockroachDB statement bundles
type Analyzer struct {
	bundlePath   string
	tempDir      string
	extractedDir string
	version      string
	isTemporary  bool
}

// New creates a new bundle analyzer
func New(bundlePath string) (*Analyzer, error) {
	a := &Analyzer{
		bundlePath: bundlePath,
	}

	if err := a.setupBundle(); err != nil {
		return nil, err
	}

	return a, nil
}

// Close cleans up temporary files
func (a *Analyzer) Close() {
	if a.isTemporary && a.tempDir != "" {
		_ = os.RemoveAll(a.tempDir)
	}
}

// setupBundle extracts or validates the bundle directory
func (a *Analyzer) setupBundle() error {
	info, err := os.Stat(a.bundlePath)
	if err != nil {
		return fmt.Errorf("bundle path does not exist: %w", err)
	}

	if info.IsDir() {
		// Already extracted directory
		a.extractedDir = a.bundlePath
		return nil
	}

	// Extract ZIP file
	tempDir, err := os.MkdirTemp("", "bundleanalyzer-*")
	if err != nil {
		return fmt.Errorf("failed to create temp directory: %w", err)
	}

	a.tempDir = tempDir
	a.isTemporary = true
	extractDir := filepath.Join(tempDir, "bundle")

	if err := extractZip(a.bundlePath, extractDir); err != nil {
		return fmt.Errorf("failed to extract bundle: %w", err)
	}

	a.extractedDir = extractDir
	return nil
}

// extractZip extracts a zip file to the specified directory
func extractZip(src, dest string) error {
	reader, err := zip.OpenReader(src)
	if err != nil {
		return err
	}
	defer func() {
		_ = reader.Close()
	}()

	if err := os.MkdirAll(dest, 0755); err != nil {
		return err
	}

	for _, file := range reader.File {
		path := filepath.Join(dest, file.Name)

		if file.FileInfo().IsDir() {
			_ = os.MkdirAll(path, file.FileInfo().Mode())
			continue
		}

		err := func() error {
			fileReader, err := file.Open()
			if err != nil {
				return err
			}
			defer fileReader.Close()

			targetFile, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, file.FileInfo().Mode())
			if err != nil {
				return err
			}
			defer targetFile.Close()

			_, err = io.Copy(targetFile, fileReader)
			return err
		}()
		if err != nil {
			return err
		}
	}

	return nil
}

// getVersionFromEnv extracts the CockroachDB version from env.sql
func (a *Analyzer) getVersionFromEnv() error {
	envPath := filepath.Join(a.extractedDir, "env.sql")

	// Try to find env.sql in subdirectories if not in root
	if _, err := os.Stat(envPath); os.IsNotExist(err) {
		err := filepath.Walk(a.extractedDir, func(path string, info os.FileInfo, err error) error {
			if err != nil {
				return err
			}
			if info.Name() == "env.sql" {
				envPath = path
				// Update extractedDir to the actual bundle directory
				a.extractedDir = filepath.Dir(path)
				return filepath.SkipDir
			}
			return nil
		})
		if err != nil {
			return fmt.Errorf("failed to find env.sql: %w", err)
		}
	}

	content, err := os.ReadFile(envPath)
	if err != nil {
		return fmt.Errorf("failed to read env.sql: %w", err)
	}

	// Look for version pattern: 'CockroachDB CCL v23.1.0 ...'
	versionRegex := regexp.MustCompile(`v(\d+\.\d+\.\d+)`)
	matches := versionRegex.FindStringSubmatch(string(content))

	if len(matches) < 2 {
		return fmt.Errorf("could not determine CockroachDB version from env.sql")
	}

	a.version = matches[1]
	return nil
}

// Analyze performs the bundle analysis
func (a *Analyzer) Analyze() (*Report, error) {
	fmt.Println(strings.Repeat("=", 70))
	fmt.Println("🔬 CockroachDB Statement Bundle Analyzer")
	fmt.Println(strings.Repeat("=", 70))
	fmt.Println()

	// Extract version
	if err := a.getVersionFromEnv(); err != nil {
		fmt.Printf("⚠️  Could not determine version: %v\n", err)
	} else {
		fmt.Printf("✓ Detected version: v%s\n", a.version)
	}

	// Find and analyze explain plans
	var allResults []AnalysisResult

	err := filepath.Walk(a.extractedDir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		if !info.IsDir() && strings.HasSuffix(strings.ToLower(info.Name()), ".txt") {
			if strings.Contains(strings.ToLower(info.Name()), "explain") ||
				strings.ToLower(info.Name()) == "plan.txt" {
				fmt.Printf("\n📊 Analyzing: %s\n", info.Name())

				content, err := os.ReadFile(path)
				if err != nil {
					fmt.Printf("⚠️  Failed to read %s: %v\n", info.Name(), err)
					return nil
				}

				results := a.analyzeExplainPlan(string(content))
				allResults = append(allResults, results...)
			}
		}

		return nil
	})

	if err != nil {
		return nil, fmt.Errorf("failed to analyze bundle: %w", err)
	}

	return a.generateReport(allResults), nil
}

// analyzeExplainPlan analyzes a single explain plan
func (a *Analyzer) analyzeExplainPlan(planContent string) []AnalysisResult {
	var results []AnalysisResult

	// Apply all analysis rules
	results = append(results, a.checkTableScans(planContent)...)
	results = append(results, a.checkJoins(planContent)...)
	results = append(results, a.checkIndexJoins(planContent)...)
	results = append(results, a.checkSorts(planContent)...)
	results = append(results, a.checkNetworkOperations(planContent)...)

	return results
}

// generateReport creates the final analysis report
func (a *Analyzer) generateReport(results []AnalysisResult) *Report {
	fmt.Println()
	fmt.Println(strings.Repeat("=", 70))
	fmt.Println("📈 ANALYSIS RESULTS")
	fmt.Println(strings.Repeat("=", 70))
	fmt.Println()

	if len(results) == 0 {
		fmt.Println("✓ No significant performance issues detected!")
		return &Report{
			Status:     "ok",
			Critical:   0,
			Warnings:   0,
			Info:       0,
			Issues:     []AnalysisResult{},
			Version:    a.version,
			BundlePath: a.bundlePath,
		}
	}

	// Group by severity
	var critical, warnings, info []AnalysisResult
	for _, result := range results {
		switch result.Severity {
		case "critical":
			critical = append(critical, result)
		case "warning":
			warnings = append(warnings, result)
		case "info":
			info = append(info, result)
		}
	}

	report := &Report{
		Status:     "issues_found",
		Critical:   len(critical),
		Warnings:   len(warnings),
		Info:       len(info),
		Issues:     results,
		Version:    a.version,
		BundlePath: a.bundlePath,
	}

	return report
}

// PrintReport prints the analysis report to stdout
func (a *Analyzer) PrintReport(report *Report) {
	if report.Critical > 0 {
		fmt.Printf("🔴 CRITICAL ISSUES (%d):\n", report.Critical)
		counter := 1
		for _, result := range report.Issues {
			if result.Severity == "critical" {
				fmt.Printf("\n  %d. %s\n", counter, result.Message)
				fmt.Printf("     Category: %s\n", result.Category)
				fmt.Printf("     💡 %s\n", result.Suggestion)
				counter++
			}
		}
	}

	if report.Warnings > 0 {
		fmt.Printf("\n🟡 WARNINGS (%d):\n", report.Warnings)
		counter := 1
		for _, result := range report.Issues {
			if result.Severity == "warning" {
				fmt.Printf("\n  %d. %s\n", counter, result.Message)
				fmt.Printf("     Category: %s\n", result.Category)
				fmt.Printf("     💡 %s\n", result.Suggestion)
				counter++
			}
		}
	}

	if report.Info > 0 {
		fmt.Printf("\n🔵 INFORMATIONAL (%d):\n", report.Info)
		counter := 1
		for _, result := range report.Issues {
			if result.Severity == "info" {
				fmt.Printf("\n  %d. %s\n", counter, result.Message)
				fmt.Printf("     💡 %s\n", result.Suggestion)
				counter++
			}
		}
	}

	fmt.Println()
	fmt.Println(strings.Repeat("=", 70))
}
