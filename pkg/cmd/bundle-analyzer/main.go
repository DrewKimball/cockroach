package main

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/spf13/cobra"
)

func main() {
	var outputJSON bool

	var rootCmd = &cobra.Command{
		Use:   "bundleanalyzer [bundle-path]",
		Short: "Analyze CockroachDB statement bundles for performance issues",
		Long: `BundleAnalyzer analyzes CockroachDB statement bundles to identify performance 
bottlenecks and suggest optimizations.

The tool can analyze either a zip file or an extracted bundle directory.`,
		Args: cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			bundlePath := args[0]

			analyzer, err := New(bundlePath)
			if err != nil {
				return fmt.Errorf("failed to create analyzer: %w", err)
			}
			defer analyzer.Close()

			report, err := analyzer.Analyze()
			if err != nil {
				return fmt.Errorf("analysis failed: %w", err)
			}

			if outputJSON {
				jsonOutput, err := json.MarshalIndent(report, "", "  ")
				if err != nil {
					return fmt.Errorf("failed to marshal JSON: %w", err)
				}
				fmt.Println(string(jsonOutput))
			} else {
				analyzer.PrintReport(report)
			}

			// Exit code 1 if issues found
			if len(report.Issues) > 0 {
				os.Exit(1)
			}

			return nil
		},
	}

	rootCmd.Flags().BoolVar(&outputJSON, "json", false, "Output results as JSON")

	if err := rootCmd.Execute(); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(3)
	}
}
