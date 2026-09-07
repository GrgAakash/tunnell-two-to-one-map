# frozen_string_literal: true

require "minitest/autorun"
require "fileutils"
require "json"
require "open3"
require "tmpdir"

class VerifyComparatorTest < Minitest::Test
  SCRIPT = File.expand_path("../scripts/verify-comparator.sh", __dir__)

  def in_project
    Dir.mktmpdir("tunnell-comparator-test") do |root|
      FileUtils.mkdir_p(File.join(root, "scripts"))
      FileUtils.mkdir_p(File.join(root, "Palomar/EntryB"))
      script = File.join(root, "scripts/verify-comparator.sh")
      FileUtils.cp(SCRIPT, script)
      yield root, script
    end
  end

  def config(root, relative, contents)
    File.write(File.join(root, relative), contents)
  end

  def test_default_config_requires_nanoda
    in_project do |root, script|
      config(root, "comparator.json", JSON.generate(enable_nanoda: false))
      _, error, status = Open3.capture3("bash", script)
      refute status.success?
      assert_includes error, File.join(root, "comparator.json")
      assert_includes error, "enable_nanoda must be exactly true"
      refute Dir.exist?(File.join(root, ".cache"))
    end
  end

  def test_selected_entry_is_checked_instead_of_root
    in_project do |root, script|
      config(root, "comparator.json", JSON.generate(enable_nanoda: true))
      selected = "Palomar/EntryB/comparator.json"
      config(root, selected, JSON.generate(enable_nanoda: false))
      _, error, status = Open3.capture3("bash", script, selected)
      refute status.success?
      assert_includes error, File.join(root, selected)
      assert_includes error, "enable_nanoda must be exactly true"
      refute Dir.exist?(File.join(root, ".cache"))
    end
  end

  def test_missing_and_malformed_selected_configs_fail_before_downloads
    in_project do |root, script|
      config(root, "comparator.json", JSON.generate(enable_nanoda: true))
      selected = "Palomar/EntryB/comparator.json"
      [nil, "{invalid"].each do |contents|
        config(root, selected, contents) unless contents.nil?
        _, error, status = Open3.capture3("bash", script, selected)
        refute status.success?
        assert_includes error, File.join(root, selected)
        assert_includes error, "cannot read valid Comparator config"
        refute Dir.exist?(File.join(root, ".cache"))
      end
    end
  end

  def test_extra_arguments_are_rejected
    in_project do |_root, script|
      _, error, status = Open3.capture3("bash", script, "one.json", "two.json")
      assert_equal 2, status.exitstatus
      assert_includes error, "usage:"
    end
  end
end
