import os, sys

def main():
    cwd = os.getcwd()
    src = os.path.join(cwd, "src")

    is_src_file = (
        lambda f: os.path.isfile(os.path.join(src, f))
        and f.endswith(".rs")
        and f != "tests.rs"
    )

    files = [file for file in os.listdir(src) if is_src_file(file)]

    with open(os.path.join(src, "tests.rs"), "w") as output:
        write_tests(src, files, output)

    os.system("cargo test " + " ".join(sys.argv[1:]))

def write_tests(src, files, output):

    get_test_name = lambda file, line: file.replace(".", "_") + f"_{line}"

    err_msg = (
        lambda file, line: f"{file} line {line} does not start with '/// ', '///', '    /// ' or '    ///'"
    )

    for file in files:
        in_test = False
        for i, line in enumerate(open(os.path.join(src, file))):
            if "/// ```" in line:
                if in_test:
                    output.write("}\n\n")
                    in_test = False
                else:
                    output.write(f"#[test]\nfn {get_test_name(file, i + 1)}() \x7b\n")
                    in_test = True
            elif in_test:
                if line.startswith("/// "):
                    output.write(f"    {line[4:].replace('rust_dsa', 'crate')}")
                elif line.startswith("///"):
                    output.write(f"    {line[3:].replace('rust_dsa', 'crate')}")
                elif line.startswith("    /// "):
                    output.write(f"    {line[8:].replace('rust_dsa', 'crate')}")
                elif line.startswith("    ///"):
                    output.write(f"    {line[7:].replace('rust_dsa', 'crate')}")
                else:
                    raise ValueError(err_msg(file, i + 1))

if __name__ == "__main__":
    main()
