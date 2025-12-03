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

// AnalysisResult represents a single performance issue found in the bundle.
type AnalysisResult struct {
	Category   string                 `json:"category"` // "scan", "join", "sort", etc.
	Message    string                 `json:"message"`
	Suggestion string                 `json:"suggestion"`
	Details    map[string]interface{} `json:"details"`
	// Performance metrics for this issue.
	KVTime         float64 `json:"kv_time,omitempty"`          // KV time in seconds.
	CPUTime        float64 `json:"cpu_time,omitempty"`         // CPU time in seconds.
	ContentionTime float64 `json:"contention_time,omitempty"`  // Contention time in seconds.
	TotalTime      float64 `json:"total_time,omitempty"`       // Total execution time in seconds.
}

// Report contains the overall analysis results.
type Report struct {
	Status     string           `json:"status"`
	Issues     []AnalysisResult `json:"issues"`
	Version    string           `json:"version,omitempty"`
	BundlePath string           `json:"bundle_path,omitempty"`
}

// Analyzer analyzes CockroachDB statement bundles.
type Analyzer struct {
	bundlePath   string
	tempDir      string
	extractedDir string
	version      string
	isTemporary  bool
}

// New creates a new bundle analyzer.
func New(bundlePath string) (*Analyzer, error) {
	a := &Analyzer{
		bundlePath: bundlePath,
	}

	if err := a.setupBundle(); err != nil {
		return nil, err
	}

	return a, nil
}

// Close cleans up temporary files.
func (a *Analyzer) Close() {
	if a.isTemporary && a.tempDir != "" {
		_ = os.RemoveAll(a.tempDir)
	}
}

// setupBundle extracts or validates the bundle directory.
func (a *Analyzer) setupBundle() error {
	info, err := os.Stat(a.bundlePath)
	if err != nil {
		return fmt.Errorf("bundle path does not exist: %w", err)
	}

	if info.IsDir() {
		// Already extracted directory.
		a.extractedDir = a.bundlePath
		return nil
	}

	// Extract ZIP file.
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

// extractZip extracts a zip file to the specified directory.
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

// getVersionFromEnv extracts the CockroachDB version from env.sql.
func (a *Analyzer) getVersionFromEnv() error {
	envPath := filepath.Join(a.extractedDir, "env.sql")

	// Try to find env.sql in subdirectories if not in root.
	if _, err := os.Stat(envPath); os.IsNotExist(err) {
		err := filepath.Walk(a.extractedDir, func(path string, info os.FileInfo, err error) error {
			if err != nil {
				return err
			}
			if info.Name() == "env.sql" {
				envPath = path
				// Update extractedDir to the actual bundle directory.
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

// Analyze performs the bundle analysis.
func (a *Analyzer) Analyze() (*Report, error) {
	fmt.Println(strings.Repeat("=", 70))
	fmt.Println("🔬 CockroachDB Statement Bundle Analyzer")
	fmt.Println(strings.Repeat("=", 70))
	fmt.Println()

	// Extract version.
	if err := a.getVersionFromEnv(); err != nil {
		fmt.Printf("⚠️  Could not determine version: %v\n", err)
	} else {
		fmt.Printf("✓ Detected version: v%s\n", a.version)
	}

	// Find and analyze explain plans.
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

// analyzeExplainPlan analyzes a single explain plan.
func (a *Analyzer) analyzeExplainPlan(planContent string) []AnalysisResult {
	var results []AnalysisResult

	// Parse the plan into a tree structure.
	planTree, err := ParsePlanTree(planContent)
	if err != nil {
		// Fall back to text-based analysis if parsing fails.
		fmt.Fprintf(os.Stderr, "Warning: failed to parse plan tree: %v\n", err)
		return results
	}

	if planTree.Root == nil {
		return results
	}

	// Apply all analysis rules with tree structure.
	results = append(results, a.checkTableScans(planTree)...)
	results = append(results, a.checkJoins(planTree)...)
	results = append(results, a.checkIndexJoins(planTree)...)
	results = append(results, a.checkSorts(planTree)...)
	results = append(results, a.checkRowProcessingEfficiency(planTree)...)

	// Populate total execution time in all results.
	totalTime := planTree.GetTotalExecutionTime()
	for i := range results {
		results[i].TotalTime = totalTime
	}

	return results
}

// generateReport creates the final analysis report.
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
			Issues:     []AnalysisResult{},
			Version:    a.version,
			BundlePath: a.bundlePath,
		}
	}

	report := &Report{
		Status:     "issues_found",
		Issues:     results,
		Version:    a.version,
		BundlePath: a.bundlePath,
	}

	return report
}

// PrintReport prints the analysis report to stdout.
func (a *Analyzer) PrintReport(report *Report) {
	if len(report.Issues) > 0 {
		// Sort issues by time impact (most expensive first).
		sortedIssues := make([]AnalysisResult, len(report.Issues))
		copy(sortedIssues, report.Issues)

		// Sort by most time-consuming first.
		for i := 0; i < len(sortedIssues)-1; i++ {
			for j := i + 1; j < len(sortedIssues); j++ {
				// Compare by KV time + CPU time.
				iTime := sortedIssues[i].KVTime + sortedIssues[i].CPUTime
				jTime := sortedIssues[j].KVTime + sortedIssues[j].CPUTime
				if jTime > iTime {
					sortedIssues[i], sortedIssues[j] = sortedIssues[j], sortedIssues[i]
				}
			}
		}

		fmt.Printf("PERFORMANCE ISSUES (%d):\n", len(sortedIssues))
		fmt.Println()

		for i, result := range sortedIssues {
			fmt.Printf("  %d. [%s] %s\n", i+1, strings.ToUpper(result.Category), result.Message)

			// Show time breakdown if available.
			if result.KVTime > 0 || result.CPUTime > 0 {
				fmt.Printf("     ⏱  ")
				if result.KVTime > 0 {
					fmt.Printf("KV: %.2fs ", result.KVTime)
				}
				if result.CPUTime > 0 {
					fmt.Printf("CPU: %.2fs ", result.CPUTime)
				}
				if result.ContentionTime > 0 {
					fmt.Printf("Contention: %.2fs ", result.ContentionTime)
				}

				// Show percentage if available.
				if timePercent, ok := result.Details["time_percentage"].(float64); ok && timePercent > 0 {
					fmt.Printf("(%.1f%% of query)", timePercent)
				}
				fmt.Println()
			}

			fmt.Printf("     💡 %s\n", result.Suggestion)
			fmt.Println()
		}
	}

	fmt.Println(strings.Repeat("=", 70))
}
