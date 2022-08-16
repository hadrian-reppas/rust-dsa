import os, sys

def main():
    if "--doc" in sys.argv or "-d" in sys.argv:
        os.system("cargo test --doc")
        return

    cwd = os.getcwd()
    src = cwd + "/src"

    is_source_file = (
        lambda f: os.path.isfile(src + "/" + f)
        and f.endswith(".rs")
        and f != "lib.rs"
    )

    files = [file for file in os.listdir(src) if is_source_file(file)]

    lib_before = open(src + "/lib.rs").read()

    try:
        with open(src + "/tests.rs", "x") as output:
            write_tests(src, files, output)
    except FileExistsError:
        print("'src/tests.rs' already exists")
        exit(1)
    except ValueError as err:
        print(err.args[0])
        os.system("rm src/tests.rs")
        exit(1)
    
    with open(src + "/lib.rs", "a") as lib:
        lib.write("\nmod tests;\n")

    if "--release" in sys.argv or "-r" in sys.argv:
        os.system("cargo test --release")
    else:
        os.system("cargo test")

    with open(src + "/lib.rs", "w") as lib:
        lib.write(lib_before)
    os.system("rm src/tests.rs")

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
