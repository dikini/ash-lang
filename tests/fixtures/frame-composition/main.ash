import @frames.codec as Codec
import @frames.frames as Frames
import @buffers.buffer as Buffer

main : Unit -> (
    Buffer.Outcome<Buffer.Outcome<Frames.DecodeResult>>,
    Buffer.Outcome<Buffer.Outcome<Frames.DecodeResult>>,
    Buffer.Outcome<Buffer.Outcome<Frames.DecodeResult>>,
    Buffer.Outcome<Buffer.Outcome<Frames.DecodeResult>>,
    Buffer.Outcome<Buffer.Outcome<Frames.DecodeResult>>
)
main () = (
    Codec.run_frame (1, Frames.Byte(0, Frames.End)),
    Codec.run_frame (2, Frames.Byte(1, Frames.Byte(0, Frames.End))),
    Codec.run_frame (2, Frames.Byte(1, Frames.Byte(255, Frames.End))),
    Codec.run_frame (3, Frames.Byte(2, Frames.Byte(0, Frames.Byte(255, Frames.End)))),
    Codec.run_frame (3, Frames.Byte(2, Frames.Byte(255, Frames.Byte(0, Frames.End))))
)
